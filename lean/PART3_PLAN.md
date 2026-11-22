# Plan: Part III in Lean

Parts I and II are machine-checked (see README.md). This is the plan for Part III of
pi_formula_theorem.md: the full class F of series
`S(ρ) = ∑_{k ≥ 1} ρ(k) 2^(-⌊k/2⌋) / k` with rational periodic `ρ`, Theorems C, D and E,
and the cheaper formula.

## What Part III proves, and what each step needs

| Step | Claim | Needs |
|---|---|---|
| Setting | `S(ρ) = (1/2i) ∑_r d_r Log(1 - r/t)`, `d` a finite Fourier transform of `ρ` | log series (have it), Fourier inversion on `ℤ/N` |
| Step 1 | `S(ρ)` is an algebraic multiple of π iff `d` is an algebraic combination of multiplicative relations among the `w_r = 1 - r/t` | **Baker's theorem** |
| Step 2 | every multiplicative relation is supported on the 24 roots `R0` (all of order dividing 120), for every period | prime ideals of `ℤ[ζ_N]`, the 20 exceptional roots (Lemma 3, Bang, the Galois table) |
| Step 3 | exactly 13 independent relations among the 24 `w_r` | 13 exact identities in `ℚ(ζ_120)`; and "no more": rank 11 of the group they generate |
| Theorem C | the patterns form a 13-dimensional space; the rational ones an 8-dimensional `V` | Steps 1-3, linear algebra |
| Theorem D | no series for a non-zero algebraic multiple of π has all its terms at `gcd(k, 120) ≥ 4` | Theorem C, finite linear algebra |
| Bailey's table | the 27 counts | Theorem C, finite linear algebra |
| Theorem E | optimum 7/24 (prime measure) and 2/3 (terms per bit) | Theorem C, and the enumeration of 6.7 million vertices |
| New formula | `π/4 = ∑ ρ(k) 2^(-⌊k/2⌋)/k` for the 120-periodic `ρ` of pi_formula_120.json | **nothing beyond what we have** |

## What Mathlib has and lacks (checked in this Mathlib)

* **Has:**
  - the cyclotomic ring of integers `ℤ[ζ_n]` for every `n`
    (`IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`);
  - Dedekind domains with `P`-adic valuations;
  - the Galois action on the primes above `p`, transitive
    (`exists_smul_eq_of_isGaloisGroup`);
  - cyclotomic Galois groups (`autEquivPow`);
  - the Taylor series of `log` (`hasSum_taylorSeries_neg_log`);
  - bounds on `π`, `log`, `cos`.
* **Lacks:**
  - Baker's theorem; Gelfond-Schneider is not in Mathlib either;
  - Lindemann-Weierstrass beyond its analytic part (only `AnalyticalPart.lean` is
    present).

  Formalizing Baker's theorem is a research-sized project (transcendence theory), far
  beyond this one.

So Part III splits in two. Part of it can be proved outright. The rest can be proved
*assuming Baker's theorem*, stated as an explicit hypothesis `BakerTheorem : Prop`. That
is how Bang's theorem and Lemma 2 were handled before they were proved here. Every
theorem that uses it will show `BakerTheorem →` in its statement, so nothing is hidden.

## Layer 1: unconditional (no Baker)

**M1. The new formula is correct: DONE (21 November 2026).** `PiFormula.new_formula_series`
in `Pilean/Pilean/PiFormula/NewFormula.lean`, standard axioms only. Before it, `PiFormula.new_formula`
checked only the *value* `2 arctan(1/3) + arctan(1/7) + Z = π/4`. M1 proves the *series*,
which is the thing the engine actually sums:

    HasSum (fun k => ρ k * 2^(-⌊k/2⌋) / k) (π/4),   ρ(k) = numerators[k mod 120] / 2.

* The proof: the decomposition (decompose_formula.py) is
  `-2 ARG(O6) + (ARG(O10) - ARG(O2)) + 2(LOG(O6) - 2 LOG(O1)) - 2(LOG(O8a) - 2 LOG(O1))
  + (LOG(O24) - LOG(O8b) - 2 LOG(O1))`. Every orbit in it is already defined in Lean:
  - `O1, O2, O6, O10` are `orbit (P 0)`, `orbit (Q 0)`, `orbit (Q 1)`, `orbit (Q 2)`;
  - `O8a, O8b, O24` are `selfOrb 0 false`, `selfOrb 0 true`, `selfOrb 1 true`.
* New pieces:
  - the `LOG` series (the real-part twin of `hasSum_gamma`);
  - the values `log |z_O|` from `zO_cycPoly`, which give `|z| = 1, 1, 3, 3` for
    `O8a, O1, O8b, O24`, so the four `LOG` relations vanish;
  - power sums of the self-paired orbits, by the rotation trick already used for the
    Ramanujan sums: `∑_{r^n = c} r^k = n c^(k/n) [n ∣ k]`.
* The term-by-term identity: `2^⌊k/2⌋ (1+i)^(-k)` has period 8, so it reduces to 120
  rational checks, done by `decide`.
* Size: roughly 600-1,000 lines. Risk: low.

**M2. Other named formulas (optional).** The same method proves the series of:
* the BBP formula of 1995;
* Bellard's formula;
* Huvent's two formulas of rate 2/3.

Those that need the √3-twisted series need individual roots of order 24, not orbits,
so they wait for M3. Size: 300-600 lines each.

**M3: DONE (21 November 2026)**, in `Relations.lean` and `VSeries.lean`, standard axioms
only:
- **The 13 relations**, in product form (`relation_1` ... `relation_13`). Each lives in
  `ℚ(ζ_20)` or `ℚ(ζ_24)` and is checked modulo `Φ_20` or `Φ_24` by `linear_combination`
  certificates.
- **The 8 named series of V**, the twisted one included: rational, period 120, with their
  values, and linearly independent (`V_lower_bound`).
- **The new formula** lies in their span (`rhoNew_eq_named`).

Left for later:
- the log form of the relations with the exact multiple of π;
- the 13-dimensional algebraic statement, which needs M6's Fourier correspondence.

The original description follows.

**M3. The 13 relations hold (Theorem C, lower bound).** Each of the 13 identities
`∏ w_r^(e_r) = root of unity` (r in R0) is checked exactly in `ℚ(ζ_120)`. From them:
- the 13 patterns have values in `Q̄ π`;
- the 8 basis patterns of `V` (pi_space_basis_120.json) have the stated rational values,
  the twisted one included.

This needs exact arithmetic in a degree-32 field. There are two options:
* (a) **Polynomial certificates.** Each identity becomes a polynomial identity modulo
  `Φ_120(ζ) = 0`, with the quotient computed by a script and checked by
  `linear_combination`.
* (b) **A small verified model.** Build `ℤ[i][X]/Φ_120` with an evaluation map, and
  check the identities by `decide`.

Option (a) is faster to start; option (b) scales better. Size: 800-1,500 lines plus the
generated certificates. Risk: kernel time.

**M4 status (21 November 2026): DONE (M4.1 and M4.2).** Step 2 of Theorem C is proved
outright: `support_subset_R0'` in `GoodPrimes.lean`, standard axioms only.

*M4.1* is `Support.lean`. It proves
`support_subset_R0 : GoodPrimes → (every relation is supported on R0)`, for relations of
any period. It works with prime ideals of the algebraic integers of `ℂ` and needs no
Dedekind theory. Its four pieces:
- **Residue lemma:** if `p ∈ P` and `u - 1 ∈ P`, then `ord u` is a power of `p`.
- **Private-prime lemma** for relations in product form.
- **Closure:** `R0` contains the `p'`-part of each of its elements for every odd prime `p`
  (`decide`).
- **The review's largest-order argument.**

*M4.2* is `GoodPrimes.lean` (about 540 lines). It proves `goodPrimes : GoodPrimes`: every
root of unity `r ∉ R0` has a prime ideal `Q` of the algebraic integers with `t - r ∈ Q`
and an odd prime `p ∤ ord r` in `Q`. How it goes:
1. **The orbit and its polynomial.** `r` lies in an explicit orbit (`exists_explicit_orbit`),
   the roots of `F = Φ_m(κ X^N)` with `κ ∈ {±1, ±i}`, `N` a power of 2. The Galois table
   gives more than the orbit: `F` made monic is the minimal polynomial of `r` over `ℚ(i)`
   (`minpoly_eq_of_mem_roots`, exported from `TheoremBGalois.lean`).
2. **Divisibility in `ℤ[i][X]`.** If `g ∈ ℤ[i][X]` and `g(r) = 0`, then `F ∣ g` in
   `ℤ[i][X]` (`dvd_of_eval₂_eq_zero`: the minimal polynomial divides `g` over `ℚ(i)`, and
   division by a monic polynomial descends along the injection `ℤ[i] → ℚ(i)`).
3. **A prime dividing the atom `F(t) = Φ_m(κ t^N)`.**
   - For the rows `P k, Q k, R k e`, use Lemma 3 (`exists_primitive_atom`) and a Gaussian
     prime `ρ ∣ atom` (`exists_prime_dvd_of_dvd_norm`).
   - For their partners the atom is the conjugate, and its norm is the same.
   - For the self-paired rows, the atom is `Φ_m(2)` or `Φ_m(-2) = Φ_{2m}(2)`. Bang gives
     an odd `q` of order `m` or `2m`, so `q ∤ m`; take any Gaussian prime `ρ ∣ q`. Bang
     gives nothing for `Φ_1(2) = 1` (`±ζ_8`) and `Φ_3(-2) = 3` (`O_24`). The orbit
     `±ζ_8^3` (atom `Φ_1(-2) = -3`) is in `R0`, so it needs no prime.
4. **Lying over, in place of Galois transport** (`exists_prime_of_kernel`). The map
   `φ : ℤ[i][X] → 𝔸`, `X ↦ r`, is integral. Its kernel lies in the prime
   `P = {g : ρ ∣ g(t)}` by steps 2 and 3. So some prime `Q` of `𝔸` has contraction `P`
   (`Ideal.exists_ideal_over_prime_of_isIntegral`). `Q` contains `φ(t - X) = t - r` and
   `φ(p) = p`. The first plan chose a prime above `ρ` first and then moved it with an
   automorphism of `Q̄` over `ℚ(i)`. Fixing `r` first makes the automorphism unnecessary.
5. **Bookkeeping** (`mem_R0_of_roots`, `decide`). The orbits left over make up exactly `R0`:
   - `{1}`, `{-1}`, `{i}`, `{-i}`;
   - the 6th, 10th, 12th and 20th roots of `R0`;
   - `{±ζ_8}`, `{±ζ_8^3}` and `O_24`.

The original description follows.

**M4. Step 2: every relation is supported on R0.** This holds for every period, which is
what makes period 120 cover all periods. It is unconditional and purely algebraic. It
breaks into five pieces:
* (i) no prime above 2 divides `t - r`;
* (ii) if a prime `P` divides `t - r` and `t - r'`, then `r'/r` has order a power of the
  residue characteristic of `P`. The image of a root of unity of order `ℓ ≠ p` is not
  1 in the residue field.
* (iii) the exceptional roots are exactly the 20 listed.
  - "Not exceptional" comes from Lemma 3 (for the rows `m, 2m, 4m, 2^(j+3) m`) and from
    Bang's theorem on `Φ_m(2)` (for the self-paired row `8m`), all proved here.
  - The step from orbits to single roots uses the Galois table (proved) and Galois
    transitivity on primes: `p ∣ N(t - r)` gives some prime above `p` dividing `t - r`.
  - "Exceptional": the norms of `t - r` for the 20 roots involve only primes dividing
    their orders.
* (iv) the largest-order argument, in the review's corrected form.
* (v) the valuation of a relation at `P` is `∑ e_r v_P(t - r) = 0`.

This is the largest milestone. Size: 2,000-4,000 lines. Risk: medium, mostly API work
with prime ideals in `𝓞 ℚ(ζ_N)`.

**M5 status (21 November 2026): DONE**, in `Rank.lean` (about 1,260 lines, 470 of them
generated by `scripts/rankgen.py`), standard axioms only. Neither option below was needed:
the proof is exact, with no numerical enclosure. What is proved:
- `basis_independent`: the 11 numbers `w_j`, `j ∈ B11 = {30, 15, 20, 45, 105, 5, 60, 90,
  12, 36, 84}`, satisfy no multiplicative relation.
- `rel1_isRel` ... `rel13_isRel`: the 13 relations of `Relations.lean`, as exponent vectors.
- `relations_span`: if `f` is a relation among the 24 numbers, then `4 f` is an integer
  combination of the 13.
- `rel_independent`: the 13 vectors are linearly independent. So the relation lattice has
  rank exactly 13 and the 24 numbers generate a group of rank 11.
- `relations_classified`: Steps 2 and 3 together, for a relation on any finite set of
  roots of unity.

How `basis_independent` goes:
1. **Galois conjugation** (`isRelJ_conj`). The embedding `ℚ(ζ_120) → ℂ`, `ζ ↦ ζ^a`, with
   `a ≡ 1 (mod 4)` fixes `t`, so it sends a relation among the `w_j` to the same relation
   among the `w_{aj}`. Mathlib supplies the embedding
   (`IntermediateField.algHomAdjoinIntegralEquiv`); no automorphism of `ℂ` is needed.
2. **Absolute values** (`sum_ell_eq_zero`). So `∑ f_j log |w_{aj}| = 0` for the 16 values
   of `a`. Conjugating by `a ≡ 1 (mod 20)` moves only the roots of order 6, 8 and 24, and
   by `a ≡ 1 (mod 24)` only those of order 10. Differences of these equations isolate the
   six roots that carry units:
   - for `ζ_24, ζ_6, ζ_8` three equations of the shape `Y + Z = X + Z = X + Y = 0`;
   - for the three roots of order 10 a 4 × 4 circulant system (`circulant_zero`).
3. **Only signs are needed.** The numbers `log |w_j|` enter only through a few
   inequalities: `|t - r| ≠ |t + r|`, `|t - r| ≠ |t - conj r|`, and
   `|t - r||t - conj r|` differs at `e^(iπ/5)` and `e^(3iπ/5)`. They follow from
   `|t - e^(iθ)|² = 3 - 2 cos θ - 2 sin θ` and the signs of `cos` and `sin`. Also
   `|t - i conj r| = |t - r|`.
4. **Private primes** for the last four roots `ζ_8^3, ζ_8^7, -1, -i`: a prime of the
   algebraic integers containing `t - r` (from `GoodPrimes.lean`) contains 3, 3, 5, 5 and
   no other `t - r'`.
5. The coefficient of `w_30 = 1/t` vanishes because `|1/t| ≠ 1`.

`relations_span` is elimination: each of the 13 relations has its own pivot root outside
`B11`, with coefficient -1, 1, 2 or 4, and besides it only the root 1 occurs among the
pivots.

The original description follows.

**M5. No more relations: the 24 `w_r` generate a group of rank 11.** This is the upper
half of Step 3. The note certifies it with the Gram determinant of valuations at primes
over 2, 3, 5 and logs of absolute values at 16 embeddings. Valuations alone cannot do
it: there are only 10 primes over 2, 3 and 5, so at least one direction is a unit and
needs an archimedean fact. There are two options:
* (a) **Certified numerics.**
  - Enclose each `log |σ(w_r)|` using Mathlib's bounds on `cos`, `π` and `log`.
  - Show that an 11 × 11 minor is far from 0. The Gram determinant is 1.5 × 10⁹ ± 0.4,
    a big margin, so modest precision is enough.
* (b) **Mostly exact.**
  - Take 10 elements with independent valuations, computed from explicit prime ideals
    of small subfields.
  - Add one unit, and show it is not a root of unity by a single numerical inequality.

Option (a) is mechanical, with a script generating the enclosures. Option (b) needs
explicit prime ideals. Size: 1,000-2,000 lines. Risk: medium.

## Layer 2: conditional on Baker's theorem

**M6 status (21 November 2026): DONE**, in `Baker.lean` (about 420 lines) and `Fourier.lean`
(about 250 lines), standard axioms only, with `BakerTheorem` an explicit hypothesis.
- `BakerTheorem` is stated for a family `lam : Fin n → ℂ` with each `exp (lam i)` algebraic,
  in the inhomogeneous form of Baker's Theorem 2.1.
- `baker_descent` avoids choosing a basis and avoids modules over `Q̄`. The span over the
  algebraic numbers is an inductive predicate (`AlgSpan`, since generalized to `SpanIn F`
  for a subfield `F`). The proof is an induction on the
  number of logarithms: if they are independent over `ℚ`, Baker gives `β = 0`; otherwise an
  integer relation `z` removes one of them (`β - (β_i/z_i) z` has one coefficient fewer).
- The logarithms are indexed by `Option ℂ`: `iπ` at `none`, `Log(1 - r/t)` at `some r`. An
  integer relation among them exponentiates to a multiplicative relation
  (`isRelation_of_intRel`), and `relations_classified` (M4 + M5) finishes `baker_step1`.
- The Fourier side works with the powers of `ζ_N = exp(2πi/N)`: `fourier_inversion`, then
  `series_eq_logs` by summing the logarithm series over the roots.
- Not done here, left to M7: the twisted equivariance of `d` that expresses "ρ rational",
  which is what turns the 13-dimensional space over `Q̄` into 13 dimensions over `ℚ`.

The original description follows.

**M6. Step 1.** First state `BakerTheorem`, the qualitative linear form in logarithms:
- *hypothesis:* `λ_1, ..., λ_n` are logarithms of algebraic numbers, linearly independent
  over ℚ;
- *conclusion:* `1, λ_1, ..., λ_n` are linearly independent over `Q̄`.

Then prove `BakerTheorem →` (`S(ρ) ∈ Q̄ π` iff `d` lies in the `Q̄`-span of relation
vectors). This needs:
* the Fourier bijection `ρ ↔ d` on `ℤ/N`, and the twisted equivariance that expresses
  "ρ rational";
* the link "`∑ e_r Log w_r ∈ 2πi ℚ` iff `∏ w_r^(e_r)` is a root of unity";
* linear algebra over `Q̄ = algebraicClosure ℚ ℂ`.

Size: 800-1,500 lines.

**M7 status (21 November 2026): DONE (parts 1, 2 and 3).**

*Part 1* is `TheoremC.lean` (about 370 lines), from `BakerTheorem`: period 120,
`dim algSpace N ≤ 13`, `8 ≤ dim ratSpace N ≤ 13` (`theoremC_bounds`). The first estimate of
500 lines for all of M7 was too low: a `Q̄`-subspace of dimension 13 bounds the rational
patterns by 13, but equality, and the count 8, need the rational structure.

*Part 2* is done as planned below, in `GaloisValue.lean`, `ExactArgs.lean`, `LogForms.lean`
(generated) and `TheoremC2.lean`, about 1,950 lines: `finrank_ratSpace` (dimension exactly 8)
and `span_namedFam` (the eight named series span). Three things came out simpler than the
plan:
- Step 3 needs no explicit coefficient vector in `K`. `baker_descent` now works over any
  subfield `F` of algebraic numbers (`SpanIn F`), so the combination of integer relations has
  its coefficients in `K = ℚ(ζ_120)`, and an embedding is applied to them directly
  (`conj_relation`). The pattern `σ_b ρ` of step 2 is never formed: the conclusion is the
  identity `∑_a d(ζ^(ba)) Log w_a = qπ` about the coefficients (`conj_value`).
- Step 1 is a table: every `arg w_j` is a rational combination of `π`, `arg w_60` and
  `arg w_5` (`garg_table`), from eight relations only. The exact multiple of any relation,
  conjugated or not, is then a finite sum (`log_exact`), so the matrices `M_b` of step 4
  are not needed.
- Step 4 uses five conjugations `b = 41, 49, 61, 73, 97` and gives the constraints
  `c_11 = c_5 - c_4 + c_10`, `c_12 = 2 c_10`, `c_6 = c_7 = c_8 = c_9`.

*Part 3* (`dim algSpace N = 13`) is done, in `FiveSeries.lean` (about 1,200 lines, two
thirds generated by `scripts/fivegen.py`) and `TheoremC3.lean` (about 500 lines): five
explicit series with values `-π/√3`, `-√2 π`, `-√5 π`, `(θ₁ - 3θ₃)π/5`, `(3θ₁ + θ₃)π/5`
(`θ₁ = 2cos(π/10)`, `θ₃ = 2cos(3π/10)`), `fam13_linearIndependent`, `finrank_algSpace`,
`theoremC`. How the five were found: the 13 relations span a space stable under
`j ↦ bj` (`b ≡ 1 mod 4`); split it by the characters of that group. The trivial
character gives the seven untwisted named series; the character of `√3` gives the
twisted named series and one more; `√2` and `√5` give one each; the two quartic
characters of `ℚ(ζ_20)/ℚ(i)` give two.

The plan for part 2, as written before it was carried out:

*M7, part 2: `dim ratSpace N = 8`.* No new series is needed.
1. **Exact multiples.** For each of the 13 relations, `∑ e_j Log w_j = μ iπ` with the exact
   `μ` (`-1/2, -1/2, -1/2, -1/2, 1/3, -5/6, -11/10, -39/10, -7/10, 17/10, -4/3, -1/6, 1/4`).
   `log_form` gives a rational `μ`; the multiplicative relation gives it modulo 2; the branch
   is fixed by `|arg w_j| ≤ π/4`, the antisymmetry `arg w_{30-j} = -arg w_j`, and a few signs.
2. **The Galois action on patterns.** For `b ≡ 1 (mod 4)` prime to `N`,
   `(σ_b ρ)(k) = (-1)^(k(b-1)/4) ρ(bk)` is again rational, and its coefficients are
   `d_{r^a}` with `ab ≡ 1`. Because `u(bk)/u(k) = (-1)^(k(b-1)/4)` for
   `u(k) = t^(k mod 2) i^⌊k/2⌋`.
3. **Rational values are Galois invariant.** If `S(ρ) = qπ` with `q` rational, then
   `S(σ_b ρ) = qπ`. Proof: on `R0` the coefficients are `d = ∑ a_k rel_k` with
   `a_k = (1/4) spanCoeff(d)_k` in `ℚ(ζ_N)`; `S(ρ) = iπ ∑ a_k μ_k`; apply the embedding
   `ζ_N ↦ ζ_N^b` of `ℚ(ζ_N)` (as in `isRelJ_conj`) to `∑ a_k μ_k = -iq`.
4. **Rank 6.** So for `ρ` with `S(ρ) = 0` the vector `a` is orthogonal to the 16 rational
   vectors `M_b μ` (`M_b` the action of `σ_b` on the relation lattice, computed by
   `spanCoeff`). These span a space of dimension 6. Checked numerically on 21 November 2026
   (the 16 × 13 matrix of exact multiples of the conjugated relations has rank 6); in Lean
   it will be a 6 × 6 minor checked by `decide`. Then `dim {S = 0} ≤ 13 - 6 = 7` and
   `dim ratSpace ≤ 8`.

*M7, part 3: `dim algSpace N = 13`.* Five more rational patterns whose series are algebraic
irrational multiples of `π`, in the style of the twisted series of `VSeries.lean`, or a
Galois-descent argument for the `Q̄`-span of the relations. (My guess for the multiples is
`√2`, `√3`, `√6` and two numbers of `ℚ(ζ_20)`. This has not been checked.)
Carried out on 21 November 2026 with five explicit series. The guess `√6` was wrong: the
third square root is `√5`.

The original description follows.

**M7. Theorem C.** M6 + M3 + M4 + M5. Exactly 13 dimensions, and exactly 8 rational ones,
at every period. Size: 500 lines.

**M8. Theorem D, and Bailey's 27 counts.** These are finite rational linear algebra on
the explicit 13- and 8-dimensional spaces, with dimension counts at sub-periods. Each
fact gets an explicit certificate (a basis and a left inverse) checked by `norm_num` or
`decide`. Size: 500-1,000 lines.

**M8 status (21 November 2026): DONE for the rational space.** `TheoremD.lean` (about 600
lines, two thirds generated by `scripts/baileygen.py`) and `Bailey.lean` (about 570 lines),
all from `BakerTheorem`, standard axioms only.

- `exists_coords`, `hasSum_namedComb`: coordinates `q ∈ ℚ^8` in the named series; value
  `(q 0 + q 2) π/4`.
- `value_formula`: the value of any `ρ ∈ ratSpace N` is
  `(7ρ(1)/12 + ρ(2)/8 + ρ(3)/6 - 7ρ(7)/12 + ρ(9)/6 - ρ(14)/8) · π/4`. This came out of the
  certificate for Theorem D and is sharper than Theorem D.
- `theoremD`, `exists_slow_term`: Theorem D for rational multiples of `π`.
- `zeroSpace_gcd`, `finrank_zeroSpace`, `finrank_zeroSpaceEven`: the number of zero
  relations at every period `n ≥ 1`, with explicit bases; only `gcd(n, 120)` matters.
- `bailey_F2`, `bailey_F1`: the 27 rows.

- `SharpD.lean` (about 200 lines, added the same day): `theoremD_sharp`, `fast_eq`,
  `finrank_fast` (the patterns with no term at `gcd(k, 120) < 4` form a line, spanned by
  `zD = -2·namedL8 + 2·namedL10 + namedL24`), and `theoremD_best_possible` (any two of the
  classes `gcd = 1, 2, 3` can be avoided; three explicit formulas, no Baker).

Theorem D for algebraic multiples is done too (`TheoremDAlg.lean`: `theoremD_alg_sharp`,
`theoremD_alg`, `exists_slow_term_alg`), with the certificate `coords13_D` on the
13-dimensional space. The re-indexing between Bailey's sums and patterns is done as well (`BaileySums.lean`,
about 490 lines: `hasSum_bailey_F2`, `hasSum_bailey_F1`, `bailey_count_F2`,
`bailey_count_F1`, `bailey_table`). Nothing is open in M8. `value_formula_check.py` recomputes the
value formula, the sharp form and the three examples exactly, independently of Lean.

## Layer 3: Theorem E (the optima), the open problem

Given Theorem C, Theorem E is a finite statement about the explicit 8-dimensional `V`.
* The definitions are easy: terms per bit, and `mean(1/s)` over the 32 classes of primes
  mod 120.
* The proof is the hard part. It enumerates 6,724,520 choices of 7 conditions out of 35,
  each a 7 × 7 determinant. That is far too much for the kernel's `decide`. There are
  three options:
  - (a) `native_decide`. This works, but it adds trust in Lean's compiler, the axiom
    `Lean.ofReduceBool`. The rest of this project uses no such axiom.
  - (b) A smaller certificate. Branch and bound on the 32 classes with symmetry
    reduction, or a structural argument that rules out most vertices. Before any Lean,
    a Python experiment would have to show the certificate is small (around 10⁵ cases
    or fewer).
  - (c) Leave it to exact_optimum.py, as now, and say so.

  Recommendation: (b) first, with (a) as a clearly labeled fallback.

**Experiment for (b), 21 November 2026 (`theorem_e_experiment.py` in `python/`).**
A branch-and-bound tree on the 35 conditions replaces the enumeration:
- The 32 classes of primes mod 120 fall into only 4 types (`c mod 12`), and the positions
  into 35 classes of proportional conditions. Proof that `mean(1/s) ≥ 7/24`: **13 nodes**.
  With the equality cases: 20 nodes, exactly two flats, as the note says.
- Proof that at least 40 of 120 entries are non-zero (terms per bit `≥ 2/3`): about
  **1,100 nodes**; with the equality cases about 1,800, exactly two vertices.
- Not tested: the third claim (the non-dominated pairs).

So (b) works and `native_decide` is not needed. The prime-measure half reduces to about a
dozen linear facts on the coordinates `q` (which conditions force which, and which force
the value 0) and can be written by hand. The fewest-terms half needs a generated
certificate or a small verified checker run by `decide +kernel`.

**Theorem E status (22 November 2026): both bounds and their attainment DONE.**
`Classes.lean` (the 35 classes, the four types), `PrimeMeasure.lean` (`primeCost_ge`,
`primeCost_rhoNew`; the 13-case tree by hand on 17 generated linear facts),
`FewestTerms.lean` (`termCount_ge`; a verified checker `checkCert` with `checkCert_sound`,
and a generated certificate of 1,517 nodes and 2,229 derived facts checked by
`decide +kernel` in under a minute), `TheoremE.lean` (`theoremE`, Huvent's two formulas in
Bailey's notation, `cost_table`). Generator: `scripts/egen.py`. Standard axioms only.

**Theorem G (22 November 2026): `log 23` has no binary BBP-type formula. DONE** in
`Log23.lean` (about 630 lines), from `BakerTheorem`: `no_rel_23` (unconditional),
`baker_no_log`, `no_log23`, and the two Bailey forms. The lemmas `coeff_eq_zero_upTo`,
`support_upTo`, `exponent_eq_zero_upTo`, `baker_no_log` are stated for any integer `ℓ`, so
the next primes (47, 53, 59, ...) need only their own `goodPrimes_ne_ℓ`. Open: a general
criterion for all primes at once, and the families with `n` other than `B`, `2B`.

**Theorem H (22 November 2026): the primes below 100. DONE** in `LogPrimes.lean` (about
430 lines) and `LogYes.lean` (about 330 lines). `log_primes_below_100` (from
`BakerTheorem`): for a prime `p < 100`, `log p` is a value of the class F exactly for the
fifteen primes 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73. The fifteen formulas
are unconditional (`isFValue_log_of_mem`); the ten exclusions use Baker. Open: a criterion
for all primes at once.

**Baker's theorem (lead, 22 November 2026).** A public branch `baker` of the GitHub fork
`mkaratarakis/mathlib4` has 19 Lean files (`Mathlib/NumberTheory/Transcendental/Baker/`)
with `Transcendental.baker`, stated exactly like `BakerTheorem` (algebraic coefficients,
`LinearIndependent ℚ l`). Its `Basic.lean` has an Apache 2.0 header and no `sorry`. It has
not been built or audited here, it is unmerged and unannounced as far as the searches
show, and it targets an earlier toolchain. If it builds against our Mathlib and
`#print axioms` is clean, `BakerTheorem` becomes a theorem and every result of Part III
becomes unconditional in Lean. The lean-eval problem "Baker-Wüstholz" is a different
statement (integer coefficients, explicit lower bound) and would not give `BakerTheorem`.

Open for Theorem E: the uniqueness statements (two formulas at `2/3`; two 2-dimensional
flats at `7/24`) and the list of non-dominated pairs. The same checker extends to them:
the leaves must then also identify the flat.

## Out of scope

* Baker's theorem itself.
* Part IV (Theorem F) until Layer 2 exists. It uses the same Baker framework plus the
  sub-series lemma.
* The claim that the prime measure is the cost of the window algorithm. That is a fact
  about the algorithm, not a theorem; Lean can state the measure, not the running time.

## Order and milestones

1. **M1** (the series of the new formula). Unconditional, low risk, and it proves the
   formula the engine uses.
2. **M3** (the 13 relations hold; the 8 basis series of `V`), with **M2** for Huvent's
   formulas along the way.
3. **M4** (support on R0), unconditional. DONE.
4. **M5** (rank 11), unconditional. DONE.
5. **M6-M8** (Baker as a hypothesis; Theorems C and D; Bailey's table). M6, M7 and M8 DONE:
   Theorem C in full (dimensions exactly 13 and 8), Theorem D for algebraic multiples, the
   value formula, Bailey's 27 counts.
6. Theorem E: run the certificate experiment first, then decide between (b), (a) and (c).

After step 4, everything about the algebraic structure of F is proved outright. After
step 5, Theorems C and D are proved from Baker's theorem alone, stated as a hypothesis.
