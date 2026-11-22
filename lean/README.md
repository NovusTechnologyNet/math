# Lean formalization of Theorems A and B

Theorem A (`notes/pi_formula_theorem.md`, Part I): every rational linear relation between pi and the
binary Machin-type generators `arctan (1/2^m)`, `arctan (1/(2^m - 1))` (`m ≥ 1`) is a
combination of R1, R2, R3.

Theorem B (Part II), in its form on representative atoms: every rational linear relation
between pi and the arguments of the atoms `Φ_m(1+i)`, `Φ_m(-1-i)`, `Φ_m(i 2^(2^j))` (`m` odd,
`j ≥ 1`) involves only `Φ_1(1+i) = i`, `Φ_3(-1-i) = i` and `Φ_1(-1-i) = Φ_5(-1-i) = -2 - i`
(the orbits `O_1`, `O_6`, `O_2`, `O_10`). In its `γ` form, over explicit orbits, the
rational relations among pi and the numbers `γ(O) = ∑_{r ∈ O} Im Log(1 - r/(1+i))` are
spanned by `γ(O) + γ(O*) = 0`, `γ(O_1) = π/4`, `γ(O_6) = 0` and `γ(O_10) - γ(O_2) = π/4`.

## Files

| File | Contents | Status |
|---|---|---|
| `Pilean/PiFormula.lean` | the formulas R1-R3 and Euler's; easy direction; Aurifeuille's identity; small cases; statements `BangTheorem`, `Lemma2`, `TheoremA`, `Goal` | proved (statements are definitions) |
| `Pilean/PiFormula/Bridge.lean` | `arctan (1/x) = arg (x + i)`; a relation `∑ c arctan (1/n) = q π` makes `W ^ den q` real (`star_pow_W_eq`) | proved |
| `Pilean/PiFormula/Gaussian.lean` | Gaussian prime above `p ≡ 1 (mod 4)`; Fact 1 (multiplicity identity); Fact 2 (`π` divides exactly one of `n ± i` iff `p ∣ n² + 1`); the private-prime theorem `coeff_eq_zero_of_private_prime` | proved |
| `Pilean/PiFormula/Orders.lean` | order of 2 modulo `p`: `p ∣ 4^n + 1`, `p ≡ 1 (mod 4)`, `p ∣ 4^m + 1 → n ∣ m` with odd quotient; `L * M = 4^n + 1`, `(2^m - 1)² + 1 = 2L`, `gcd(L, M) = 1` | proved |
| `Pilean/PiFormula/Bang.lean` | Bang's theorem, from the vendored Tau Ceti library | proved |
| `Pilean/PiFormula/TheoremA.lean` | the "largest index" argument (`exists_private_prime`, `coeff_eq_zero_of_not_special`); irrationality of `arctan (1/2) / π`; the last step (`four_generators`); the assembly `goal : Goal`, i.e. Bang + Lemma 2 imply Theorem A; `theoremA_of_lemma2 : Lemma2 → TheoremA` | proved |
| `Pilean/PiFormula/Lemma2.lean` | Lemma 2: the reduction (a divisor of `Φ_{4n}(2)` above `n` has a prime of order `4n`); `A_n = N(Φ_n(1+i))` divides `N((1+i)^n - 1)`, `A'_n = N(Φ_n(-1-i))` divides `N((1+i)^n + 1)`; these two norms are `L_n`, `M_n` in some order; `Φ_{2n}(X) = Φ_n(-X)` for odd `n > 1` (new, not in Mathlib); `A_n A'_n = Φ_{4n}(2)`; the size bound `A_n, A'_n > n` for odd `n ≥ 7`; small cases `M_1, M_3, M_5`; assembly `lemma2 : Lemma2` and `theoremA : TheoremA` | proved |
| `Pilean/PiFormula/TheoremB.lean` | Theorem B on representatives: the bridge and the private-prime theorem for arbitrary Gaussian integers (`star_pow_Wz_eq`, `coeff_eq_zero_of_private_prime_gen`); the atoms; Lemma 3 (every non-exceptional atom has a prime `p` of order equal to its index, from Lemma 2 or Bang, `exists_primitive_atom`; a Gaussian prime above `p` divides it but not its conjugate, and no other atom of smaller or equal index, `not_dvd_star_atom`, `private_of_max`); the largest-index argument; `theoremB : TheoremB` and `theoremB_converse` | proved |
| `Pilean/PiFormula/TheoremBGamma.lean` | `γ(O)` exactly as in the note; `γ(O) ≡ arg z_O - \|O\| π/4 (mod 2π)` (`gamma_angle`); `γ(O*) = -γ(O)` (`gamma_partner`); `\|g(r)\| ≤ π/4`; the explicit orbits (roots of `Φ_m(κ X^N)`: `orbit_P`, `orbit_Q` show they are the primitive `m`-th and `2m`-th roots; `orbit_nodup`; `κ^φ(m) z_O = atom`); the self-paired orbits of order `8m` and `γ = 0` for them; exact `γ(O_1), γ(O_2), γ(O_6), γ(O_10)`; `theoremBgamma : TheoremBgamma` and `theoremBgamma_relations` | proved |
| `Pilean/PiFormula/TheoremBGalois.lean` | the Galois table: `ℚ(i)` inside `ℂ`; the degree bound `φ(n) ≤ 2 deg minpoly_{ℚ(i)} r`; `galOrbit` and `mem_galOrbit_iff` (the note's definition of an orbit); each explicit orbit is a Galois orbit (`galOrbit_typeA`, `galOrbit_typeB`, `partner_cycPoly`); every root of unity lies in one (`exists_explicit_orbit`); the minimal polynomial itself (`minpoly_eq_of_mem_roots`); `galois_table`, `mem_orbit_iff_minpoly` | proved |
| `Pilean/PiFormula/TheoremBSpeed.lean` | Corollaries B1 and B2: the series of `γ` (`hasSum_gamma`); Ramanujan sums `c_2, c_6, c_10`; `E(k)` and its table by `gcd(k, 30)`; `Im((1+i)^(-k)) = 0` iff `4 ∣ k`; partner series cancel and self-paired series vanish term by term; `series_of_relation` (B1); `speed`, `speed_le_three_halves`, `speed_eq_three_halves_iff`, `corollaryB2` (B2) | proved |
| `Pilean/PiFormula/NewFormula.lean` | Part III, M1: the `LOG` series and `LOG(O) = log \|z_O\| - \|O\| log \|t\|`; power sums over `X^n = c` and the self-paired orbits `O_8a, O_8b, O_24`; the integer model `NZ` and its 120 checks; `new_formula_series` (the series of the new formula sums to π/4) | proved |
| `Pilean/PiFormula/Relations.lean` | Part III, M3: `ζ_120`, `ζ_20`, `ζ_24` with `Φ_20(ζ_20) = 0`, `Φ_24(ζ_24) = 0`; the 13 multiplicative relations `relation_1` ... `relation_13`, exactly | proved |
| `Pilean/PiFormula/VSeries.lean` | Part III, M3: patterns from `ℤ[i]` models; the 8 named series of V with their values; the twisted series (`√3 = ζ_24^2 - ζ_24^10`, power sums, value 0); period 120; linear independence; `V_lower_bound`; `rhoNew_eq_named` | proved |
| `Pilean/PiFormula/Support.lean` | Part III, M4.1: prime ideals of the algebraic integers (`InP`); the residue lemma; relations and the private-prime lemma; `R0` and its closure under `p'`-parts; `support_subset_R0 : GoodPrimes → ...` | proved |
| `Pilean/PiFormula/GoodPrimes.lean` | Part III, M4.2: `ℤ[i]` inside the algebraic integers and inside `ℚ(i)`; a polynomial of `ℤ[i][X]` vanishing at `r` is a multiple of `Φ_m(κ X^N)` (`dvd_of_eval₂_eq_zero`); lying over for `X ↦ r` (`exists_prime_of_kernel`); a good prime for every non-exceptional orbit (Lemma 3, Bang); the orbits left over make up the 24 roots of `R0`; `goodPrimes : GoodPrimes`; `support_subset_R0'` (Step 2 of Theorem C, unconditional) | proved |
| `Pilean/PiFormula/Rank.lean` | Part III, M5: relations indexed by exponents (`IsRelJ`); Galois conjugation of a relation (`isRelJ_conj`); the equations `∑ f_j log \|w_{aj}\| = 0`; `\|t - ζ^j\|²` and its signs; private primes for `ζ_8^3, ζ_8^7, -1, -i`; `basis_independent`; the 13 relations as exponent vectors; `relations_span`, `rel_independent`, `relations_classified` | proved |
| `Pilean/PiFormula/Baker.lean` | Part III, M6: `BakerTheorem` (a hypothesis, not proved); `baker_descent`; the logarithms `Log(1 - r/t)` and `iπ`; `baker_step1` (Step 1 of Theorem C); `log_form`, `step1_converse` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/Fourier.lean` | Part III, M6: the twisted pattern; Fourier inversion on `ℤ/N`; `series_eq_logs` (`S(ρ) = ∑ d_r Log(1 - r/t)`); `series_step1`, `series_step1_real`; `new_formula_step1` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/TheoremC.lean` | Part III, M7 part 1: `algSpace`, `ratSpace`; `twist_eq_sum` (the pattern from its coefficients); `period_120`; `rat_dependence`; `rank_algSpace_le`; `le_rank_ratSpace`; `theoremC_bounds` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/GaloisValue.lean` | Part III, M7 part 2: `K = ℚ(ζ_120)` and its embeddings `ζ ↦ ζ^b`; `conj_relation` (conjugating the coefficients of a relation among logarithms); `baker_galois`; the coefficients of a rational pattern lie in `K` (`coeffK`); `conj_value` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/ExactArgs.lean` | Part III, M7 part 2: `garg j = arg w_j`; bounds, partner symmetry, signs; `argsum_of_prod`, `pin`; eight exact argument identities; `garg_table`; `log_exact`; `isRelJ_comp` | proved |
| `Pilean/PiFormula/LogForms.lean` | Part III, M7 part 2 (generated): the exact multiples of `iπ` of the 13 relations and of their conjugates by `b = 41, 49, 61, 73, 97` (`lf_b_l`, `conjlog_b`) | proved |
| `Pilean/PiFormula/TheoremC2.lean` | Part III, M7 part 2: `conj_value_coeff`; `constraintSpace` and `finrank_constraintSpace_le`; `coeff_mem_constraintSpace`; `dependent_of_coeffs`; `finrank_ratSpace` (dimension exactly 8); `span_namedFam` | proved (from `BakerTheorem`) |
| `Pilean/PiFormula/TheoremD.lean` | Part III, M8: coordinates in the eight named series (`exists_coords`, `hasSum_namedComb`); generated certificates (`coords_p8` ... `coords_D`); `value_formula`; `theoremD` and `exists_slow_term` (Theorem D for rational multiples of `π`) | proved (from `BakerTheorem`) |
| `Pilean/PiFormula/Bailey.lean` | Part III, M8: `zeroSpace n`, `zeroSpaceEven n`; explicit bases (`zeroSpace_8` ... `zeroSpace_120`); `zeroSpace_gcd`; `finrank_zeroSpace`; `finrank_zeroSpaceEven`; Bailey's 27 rows (`bailey_F2`, `bailey_F1`) | proved (from `BakerTheorem`) |
| `Pilean/PiFormula/SharpD.lean` | Part III, M8: `zD = -2·namedL8 + 2·namedL10 + namedL24` and its support (`zD_supp`, `zD_at_5`); `theoremD_sharp`, `fast_eq`, `finrank_fast` (the sharp form of Theorem D); `theoremD_best_possible` (three explicit formulas, no Baker) | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/FiveSeries.lean` | Part III, M7 part 3: twisted power sums with real coefficients (`lsum`, `hasSum_rhoA_of_lsum`); `√2`, `√3`, `√5`, `2cos(π/10)`, `2cos(3π/10)` as sums of roots of unity; five tables with certificates modulo `Φ_24` and `Φ_20` (generated); the five patterns `extraS3`, `extraS2`, `extraS5`, `extraT1`, `extraT2` and their values (`hasSum_extraS3` ... `hasSum_extraT2`) | proved |
| `Pilean/PiFormula/TheoremC3.lean` | Part III, M7 part 3: `comb13`; values at 18 positions and the inverse matrix (generated); `fam13_linearIndependent`; `finrank_algSpace` (dimension exactly 13); `span_algFam`, `exists_coords13`; `theoremC` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/TheoremDAlg.lean` | Part III, M8: Theorem D for algebraic multiples of `π` (`theoremD_alg_sharp`, `theoremD_alg`, `exists_slow_term_alg`, `fast_alg_eq`) | proved (from `BakerTheorem`) |
| `Pilean/PiFormula/BaileySums.lean` | Part III, M8: Bailey's double sum (`baileyBlock`) and his zero relations (`baileyZero B n`); convergence and grouping into blocks (`summable_seriesTerm`, `hasSum_blocks_iff`); the patterns of a coefficient vector (`patF2`, `patF1`); `hasSum_bailey_F2`, `hasSum_bailey_F1`; `finrank_baileyZero_F2`, `finrank_baileyZero_F1`; `bailey_count_F2`, `bailey_count_F1`; `bailey_table` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/Classes.lean` | Theorem E, foundation: the 35 classes of zero conditions (`clsIdx`, `clsForm`, `class_table`, `namedComb_class`, `namedComb_eq_zero_iff`); the four types of units (`typeRep`, `type_table`) | proved |
| `Pilean/PiFormula/PrimeMeasure.lean` | Theorem E, prime measure: `firstNZ`, `primeCost`; `primeCost_namedComb` (four types); 17 linear facts (generated); `prime_sum_ge` (the 13-case tree); `primeCost_ge`; `primeCost_rhoNew` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/FewestTerms.lean` | Theorem E, standard measure: `termCount`; certificates (`Cert`), the checker `checkCert` and `checkCert_sound`; the certificate `theCert` (generated, 1,517 nodes) and `theCert_ok`; `termCount_ge` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/TheoremE.lean` | Theorem E: Huvent's two formulas in Bailey's notation (`huvent1_formula`, `huvent2_formula`) with 40 terms each; `cost_table`; `theoremE` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/Log23.lean` | Theorem G: relations up to a power of an integer (`IsRelUpTo`, `coeff_eq_zero_upTo`, `exponent_eq_zero_upTo`, `support_upTo`); good primes of characteristic other than 23 (`goodPrimes_ne_23`); `no_rel_23`; Baker's theorem with one more logarithm (`baker_no_log`); `no_log23`, `bailey_no_log23_F2`, `bailey_no_log23_F1` | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/LogPrimes.lean` | `IsFValue`; the argument of `Log23.lean` for any prime with a partner (`goodPrimes_ne`, `no_rel_of_goodPrimes`, `not_isFValue_log`); orders of 2 (`ord_two_47`, ...), three atoms (`atom_P6`, `atom_Q6`, `atom_R11`), `good_23` ... `good_97`; `not_isFValue_log_of_mem`: no formula for 23, 47, 53, 59, 67, 71, 79, 83, 89, 97 | proved (from `BakerTheorem` where stated) |
| `Pilean/PiFormula/LogYes.lean` | The values of F are a rational vector space (`IsFValue.add`, `IsFValue.const_mul`); the roots of `X^n = c` (`psum_nthRoots`, `zO_nthRoots`, `isFValue_gen`, `isFValue_log_of_gen`); the fifteen primes (`isFValue_log_2` ... `isFValue_log_73`, `isFValue_log_of_mem`); `isFValue_log_23_add_log_89`; `log_primes_below_100` | proved (the classification from `BakerTheorem`; the fifteen formulas unconditionally) |
| `Pilean/PiFormula/BakerBridge.lean` | `bakerTheorem_of_linearIndependent`: a library-style statement of Baker's theorem gives `BakerTheorem` | proved |
| `Baker/` | Baker's theorem (`Transcendental.baker`), 19 files by Michail Karatarakis (Apache-2.0), see `Baker/README.md` | builds with three one-line adjustments; standard axioms only |
| `Pilean/PiFormula/Arctan.lean` | Theorem I: relations up to a power of `a / b` (`IsRelUpToQ`, `coeff_eq_zero_upToQ`, `exponent_eq_zero_upToQ`, `support_upToQ`, `no_rel_gaussian`); Baker's theorem with one more logarithm (`baker_no_extra`); `exp_two_arctan`; `no_arctan_of_goodPrimes`, `not_isFValue_arctan`; `no_arctan_two_sevenths`, `not_isFValue_arctan_two_sevenths`, `..._five_eighths`, `..._four_ninths`, the Bailey forms; the positive half `exp_gamma`, `isFValue_arctan_inv_129`, `isFValue_arctan_two_sevenths_add` | proved (the exclusions from `BakerTheorem`; the positive half unconditionally) |
| `Pilean/PiFormula/CheckedPair.lean` | Theorem J: `pairCost`, `zCost`, `pairCost_eq_zCost`; the certificate checker `checkPair` and `checkPair_sound`; the certificate `pairCert` (about 31,000 generated lines) and `pairCert_ok`; `pairCost_ge`; Takahashi's formulas in Bailey's notation (`takahashi1_formula`, `takahashi2_formula`), `pairCost_takahashi`, `pairCost_huvent`, `checkedPair` | proved (the bound from `BakerTheorem`; the kernel check takes about four minutes) |
| `Pilean/PiFormula/LogCriterion.lean` | Theorem K, in part: `fValues` (the values of F as a rational vector space), `logSpan_le_fValues`; `isFValue_log_two_pow_sub_one`, `isFValue_log_L`, `isFValue_log_M`; the pair 433, 38737: `atom_R40`, `good_433`, `good_38737`, `not_isFValue_log_433`, `not_isFValue_log_38737`, `isFValue_log_433_add_log_38737` | proved (the two exclusions from `BakerTheorem`) |
| `Pilean/PiFormula/LogConverse.lean` | Theorem K, the converse: `aeval_pow_of_coprime`, `cleared_conj` (conjugating a cleared relation); `sum_log_coset_mem`, `sum_log_mod_four_mem`, `sum_filter_coprime`, `sum_log_coprime_mem` (sums of `log \|t - r^a\|` in `logSpan`); `log_sub_mem_logSpan_of_cleared`; `mem_logSpan_of_isFValue_log`, `isFValue_log_iff`, `isFValue_log_nat_iff`, `isFValue_log_rat_iff` | proved (from `BakerTheorem`) |
| `Pilean/PiFormula/LogExplicit.lean` | Theorem K in elementary terms: `baseNumbers`, `baseSpan`; `gaussian_unit_cases`, `tG_pow_even`, `norm_even_cases`, `norm_odd_cases`; `logSpan_eq_baseSpan`; `log_mem_span_iff_pow`; `isFValue_log_of_pow` (no Baker), `isFValue_log_rat_iff_pow` (from `BakerTheorem`) | proved |
| `Pilean/PiFormula/LogPrimeTest.lean` | Theorem K, the finite test for a prime: `isFValue_log_cyclotomic_two`, `isFValue_log_Aplus`, `isFValue_log_Aminus` (the logarithms of the primitive parts are values); `orderOf_two_of_not_dvd`, `le_of_dvd_cyclotomic` (prime divisors of `Φ_n(2)`); `dvd_norm_atom_R`, `not_dvd_norm_P_and_Q`; `primPart`, `primPart_facts`; `not_isFValue_log_of_partner`; `isFValue_log_prime_iff`, `primPart_intrinsic_unique`, `isFValue_log_prime_iff_explicit`; `isFValue_log_151`, `isFValue_log_331`, `isFValue_log_1321`, `isFValue_log_of_dvd`; `isFValue_log_prime_classification` | proved (the exclusions from `BakerTheorem`) |
| `Pilean/PiFormula/Unconditional.lean` | `bakerTheorem`; Theorems C, D, E, G, H, I, J, K, the value formula and Bailey's counts with no hypothesis (`PiFormula.Unconditional.*`, 34 theorems) | proved |
| `Pilean/Base3/Series.lean` | Base 3: `t3 = √-3`, the class F3 (`seriesTerm3`, `IsF3Value`, `f3Values`), `series_eq_logs3` (the series as a combination of `Log(1 - r/t)`), `IsRel3`, `cleared3`, `baker_no_extra3` | proved (the last from `BakerTheorem`) |
| `Pilean/Base3/LogValues.lean` | Base 3: the cube root of unity `w3`, `rhoGen`, `hasSum_gen3`, `isF3Value_log_gen` (`log \|t^n - c\|` is a value for `c^3 = 1`), `isF3Value_log_three` | proved |
| `Pilean/Base3/LogConverse.lean` | Base 3: `logSpan3`, `logSpan3_le_f3Values`; `cleared_conj3`, `sum_log_coset_mem3`, `sum_log_mod_three_mem`, `sum_log_coprime_mem3`, `log_sub_mem_logSpan3_of_cleared`; `mem_logSpan3_of_isF3Value_log`, `isF3Value_log_rat_iff` | proved (from `BakerTheorem`) |
| `Pilean/Base3/LogExplicit.lean` | Base 3: `baseNumbers3`, `norm_sq_even`, `norm_sq_odd`, `logSpan3_eq_baseSpan3`, `isF3Value_log_of_pow` (no Baker), `isF3Value_log_rat_iff_pow` (from `BakerTheorem`); `isF3Value_log_2`, `_5`, `_7`, `_11`, `_13`, `_19`, `_37` | proved |
| `Pilean/Base3/PiSqrt3.lean` | Base 3: `hasSum_gregory3`, `isF3Value_pi_sqrt3` | proved |
| `Pilean/Base3/Unconditional.lean` | Base 3: the criterion with no hypothesis (`PiFormula.Base3.Unconditional.*`) | proved |
| `TauCeti/` | 25 modules of Tau Ceti (Apache-2.0), see `TauCeti/VENDORED.md` | builds unchanged |

There is no `sorry` anywhere. `theoremA`, `theoremB`, `theoremBgamma`, `lemma2`, `size_bound` and every other theorem
depend only on `propext`, `Classical.choice` and `Quot.sound` (checked with
`#print axioms`; `native_decide` is not used, so the kernel checks the computation too).

**So Theorem A is machine-checked, unconditionally.** The formal statement `TheoremA` (in
`Pilean/PiFormula.lean`) says: if `∑ b_m arctan (1/2^m) + ∑ a_m arctan (1/(2^m - 1)) = q π` with
finitely many rational coefficients (indices `m ≥ 1`), then `b_m = 0` for `m ≥ 2`,
`a_m = 0` for `m ≥ 4`, `b_1 - a_2 + 2 a_3 = 0` and `q = (a_1 + a_2 - a_3)/4`. With
`combination_is_relation` (the converse) this is the full classification. What is left
to trust is that this statement says what the note's Theorem A says.

**Theorem B is machine-checked in its form on representatives.** The formal statement
`TheoremB` (in `TheoremB.lean`) says: if `∑ c_a arg (atom a) = q π` with finitely many
rational coefficients, over the atoms `P k = Φ_m(1+i)`, `Q k = Φ_m(-1-i)`,
`R k e = Φ_m(i 2^(2^(e+1)))` (`m = 2k + 1`), then `c_a = 0` except for `P 0`, `Q 0`, `Q 1`,
`Q 2`; `c(Q 0) + c(Q 2) = 0`; and `q = (c(P 0) + c(Q 1))/2`. `theoremB_converse` is the
converse.

**Theorem B is machine-checked in its `γ` form, over explicit orbits.** `TheoremBgamma` (in
`TheoremBGamma.lean`) uses `γ(O) = ∑_{r ∈ O} Im Log(1 - r/(1+i))` as in the note. The orbits
are explicit multisets of roots of unity:
- `orbit a`, the roots of `Φ_m(κ X^N)`. For `P k` this is the set of primitive `m`-th
  roots (`O_m`), for `Q k` the primitive `2m`-th roots (`O_2m`), and for `R k e` an orbit
  of order `2^(e+4) m`.
- the partners `partner (orbit a)`.
- the self-paired orbits `selfOrb k b` of order `8m`.

Take a relation
`∑ c_a γ(orbit a) + ∑ d_a γ(partner (orbit a)) + ∑ e_s γ(selfOrb s) = q π` with rational
coefficients. Then `c_a = d_a` for every non-exceptional `a`,
`(c - d)(Q 0) + (c - d)(Q 2) = 0`, and `q = ((c - d)(P 0) - (c - d)(Q 0))/4`.
`theoremBgamma_relations` is the converse: `γ(O) + γ(O*) = 0`, `γ(selfOrb) = 0`,
`γ(O_1) = π/4`, `γ(O_6) = 0`, and `γ(O_10) - γ(O_2) = π/4`.

**The Galois table is machine-checked.** The note defines an orbit as a class of roots of
unity with the same minimal polynomial over `ℚ(i)`. `galOrbit r` (in `TheoremBGalois.lean`)
is the root multiset of `minpoly ℚ(i) r`, and `galois_table` proves two things. First,
every explicit multiset is such a class (`mem_orbit_iff_minpoly` and its two companions
state this in the note's words). Second, the orbit of every root of unity is one of them.

## Part II: what is and is not formal

**Theorem B, as the note states it, is fully machine-checked.** It is the combination of
`theoremBgamma` (the relations among pi and the `γ` of the explicit orbits) and
`galois_table` (the explicit orbits are all the Galois orbits over `ℚ(i)`). Every step is
formal:
- the angle identity `γ(O) ≡ arg z_O - |O| π/4` (`gamma_angle`);
- the pairing (`gamma_partner`);
- the atoms `κ^φ(m) z_O = atom` (`zO_orbit`);
- the irreducibility of `Φ_m(κ X^N)` over `ℚ(i)`. This comes from the degree bound
  `φ(n) ≤ 2 deg minpoly_{ℚ(i)} r` for a primitive `n`-th root of unity in `ℚ(i)(r)`.
- the partition of all roots of unity into the explicit orbits;
- Lemma 3;
- the largest-index argument.

**Corollaries B1 and B2 are machine-checked too** (`TheoremBSpeed.lean`):
- **The series.** `γ(O) = ∑_k τ_k(O)`, with `τ_k(O) = -Im(p_k(O) (1+i)^(-k))/k` and
  `p_k(O) = ∑_{r ∈ O} r^k`, from the Taylor series of `log` (`hasSum_gamma`).
- **B1, series form.** In any relation `= q π`, the partner series cancel term by term and
  the self-paired series vanish. So the series of the combination is, term by term, that
  of `α γ(O_1) + β γ(O_6) + δ (γ(O_10) - γ(O_2))`, with `α, β, δ` the net coefficients
  (`series_of_relation`).
- **The terms.** `T(k) = -E(k) Im((1+i)^(-k))/k`, with
  `E(k) = α + β c_6(k) + δ (c_10(k) - c_2(k))` (`termB_eq`). The Ramanujan sums are
  computed for every `k` (`ramanujan_two`, `ramanujan_six`, `ramanujan_ten`). `E(k)`
  depends only on `gcd(k, 30)` (`Ek_gcd`), with the note's table (`Ek_table`), and
  `Im((1+i)^(-k)) = 0` iff `4 ∣ k`.
- **Speed**, defined as in the note: `s/2`, with `s` the least `gcd(k, 60)` of a non-zero
  term (`speed`).
- **B2.** For every series for pi in the class (`corollaryB2`, `q ≠ 0`), the speed is at
  most `3/2`, and it equals `3/2` iff `α = 0` and `β = -2δ`, which is Euler's formula up to
  scaling. Its value is `δ π/4 = δ (2 arctan(1/3) + arctan(1/7))` (`value_of_fastest`).

What is not a theorem: that this speed measures the bits gained per unit of denominator.
That is the note's convention, motivated by the terms with `k = s p`, `p` a large prime.

## Part III

The plan is in `PART3_PLAN.md`. Done so far: **M1, the new formula**. `new_formula_series`
(in `NewFormula.lean`) proves

    π/4 = ∑_{k ≥ 1} ρ(k) 2^(-⌊k/2⌋) / k,   ρ(k) = numerators[k mod 120] / 2,

with `ρ` exactly the 120 numerators of pi_formula_120.json, the series the native engine
sums. The proof follows decompose_formula.py:
- **The decomposition.** Write the formula as
  `-2 ARG(O_6) + (ARG(O_10) - ARG(O_2)) + 2(LOG(O_6) - 2 LOG(O_1)) - 2(LOG(O_8a) -
  2 LOG(O_1)) + (LOG(O_24) - LOG(O_8b) - 2 LOG(O_1))`, over orbits already defined in
  Part II.
- **The value.** The `LOG` combinations vanish because `LOG(O) = log |z_O| - |O| log |t|`
  and `|z_O| = 1, 1, 1, 3, 3`.
- **The terms.** `2 · 2^⌊k/2⌋ k` times the `k`-th term is an integer `N(k)` computed in
  `ℤ[i]`, of period 120. Its 120 values are checked against the numerators by `decide`.

**M3, the lower half of Theorem C**, is also done, in two files:
- **`Relations.lean`: the 13 multiplicative relations.** Each is proved exactly, in the form
  `∏ (t - ζ^j)^(e_j) = ζ^m ∏ (t - ζ^j)^(…)` with `ζ = ζ_120`. Every relation lives in
  `ℚ(ζ_20)` or `ℚ(ζ_24)`, so each is a polynomial identity modulo `Φ_20` or `Φ_24`, checked
  by `linear_combination` with quotients computed by sympy. The largest certificate, for
  relation 8, has degree 120.
- **`VSeries.lean`: the space V.** The 8 named series that span V have rational patterns of
  period 120 (`named_periodic`). Their values are `π/4, 0, π/4, 0, 0, 0, 0, 0`, and they
  are linearly independent over ℚ (`V_lower_bound`). This includes the √3-twisted series:
  - `√3 = ζ_24^2 - ζ_24^10` (`dTW_eq`);
  - its power sums form 24 Gaussian integers, each checked modulo `Φ_24`;
  - its value is 0, by the pairing and three explicit arguments (`π/6`, `-π/6`, `π/6`).

  The new formula's pattern is `-2 A6 + A10 + 2 L6 - 2 L8 + L24` (`rhoNew_eq_named`).

Not done in M3: the log form `∑ e_j Log w_j = c · iπ` of the relations with the exact
multiple of π (only the product form is proved), and the 13-dimensional algebraic space,
which needs the Fourier correspondence of M6.

**M4.1, Step 2 from good primes**, is also done (`Support.lean`). `support_subset_R0`
proves that every multiplicative relation, at any period, is supported on the 24 roots
`R0`, given `GoodPrimes` (each root of unity outside `R0` has a good prime). It uses:
- prime ideals of the algebraic integers of `ℂ`;
- the residue lemma;
- the private-prime argument;
- the closure of `R0` under `p'`-parts (`decide`);
- the review's largest-order argument.

**M4.2, the good primes**, is done too (`GoodPrimes.lean`), so Step 2 of Theorem C is
proved outright: `support_subset_R0'` says that every multiplicative relation among the
`1 - r/t`, at any period, is supported on the 24 roots of `R0`. `goodPrimes` gives every
root of unity `r` outside `R0` a prime ideal `Q` of the algebraic integers with
`t - r ∈ Q` and an odd prime `p ∤ ord r` in `Q`. The proof:
- `r` is a root of `F = Φ_m(κ X^N)`, and `F` made monic is the minimal polynomial of `r`
  over `ℚ(i)` (`minpoly_eq_of_mem_roots`, from the Galois table). So a polynomial of
  `ℤ[i][X]` vanishing at `r` is a multiple of `F` in `ℤ[i][X]`.
- `F(t)` is an atom of Theorem B. If a Gaussian prime `ρ` divides it, the kernel of
  `ℤ[i][X] → 𝔸`, `X ↦ r`, lies in the prime `{g : ρ ∣ g(t)}`. Lying over
  (`Ideal.exists_ideal_over_prime_of_isIntegral`) gives `Q`. It contains `t - r`, the
  image of `t - X`. No Galois automorphism is used.
- `ρ` comes from Lemma 3 (`exists_primitive_atom`) for the orbits of the atoms and their
  partners, and from Bang's theorem for the self-paired orbits, whose atom is `Φ_m(2)` or
  `Φ_m(-2) = Φ_{2m}(2)`.
- The orbits left over (`O_1, O_2, O_6, O_10`, their partners, and the self-paired
  orbits `{±ζ_8}`, `{±ζ_8^3}`, `O_24`) make up exactly `R0` (`decide`). Nothing is asked
  of the roots of `R0`.

**M5, the rank**, is done as well (`Rank.lean`): the 13 relations of `Relations.lean` are
all the relations among the 24 numbers `w_j = 1 - ζ^j/t`.
- `basis_independent`: 11 of the numbers satisfy no relation.
- `relations_span`: for every relation `f`, `4 f` is an integer combination of the 13.
- `rel_independent`: the 13 are linearly independent, so the 24 numbers generate a group
  of rank 11.
- `relations_classified`: Steps 2 and 3 together. A relation on any finite set of roots
  of unity vanishes outside `R0`, and 4 times its part on `R0` is a combination of the 13.

The note certifies the rank by a numerical Gram determinant. The Lean proof is exact and
uses no numerics:
- A relation stays a relation under `ζ ↦ ζ^a` for `a ≡ 1 (mod 4)` (`isRelJ_conj`, from
  the embedding of `ℚ(ζ_120)` that Mathlib provides).
- Taking absolute values gives 16 linear equations in the numbers `log |w_j|`. Their
  differences kill the coefficients of the six roots that carry units. Only the signs of
  a few differences of the `log |w_j|` are needed, and they come from
  `|t - e^(iθ)|² = 3 - 2 cos θ - 2 sin θ`.
- The roots `ζ_8^3, ζ_8^7, -1, -i` each have a private prime (above 3, 3, 5, 5).
- The last coefficient, of `1/t`, vanishes because `|1/t| ≠ 1`.

So Steps 2 and 3, the algebraic input to Theorem C, are machine-checked.

**M6, Step 1 from Baker's theorem**, is done (`Baker.lean`, `Fourier.lean`). Baker's theorem
is not in Mathlib and is not proved here. It is the proposition `BakerTheorem`, and every
theorem that uses it has `BakerTheorem →` in its statement; `#print axioms` shows only the
three standard axioms.

`BakerTheorem` is Theorem 2.1 of Baker's *Transcendental Number Theory*: if `λ_1, ..., λ_n`
are logarithms of algebraic numbers (each `exp λ_i` is algebraic) and are linearly
independent over `ℚ`, then `1, λ_1, ..., λ_n` are linearly independent over the algebraic
numbers.

What is proved from it:
- `baker_descent`: for logarithms of algebraic numbers, not assumed independent, a relation
  `∑ β_i λ_i = 0` with algebraic `β_i` is a combination, with algebraic coefficients, of
  integer relations. The proof removes one dependent logarithm at a time.
- `baker_step1`: if `∑_{r ∈ S} d_r Log(1 - r/t) = γ π` with `d_r`, `γ` algebraic and `S` any
  finite set of roots of unity, then `d` vanishes outside `R0`, and on `R0` it is a
  combination of the 13 relations with algebraic coefficients. (An integer relation among
  the logarithms and `iπ` is a multiplicative relation; then `relations_classified`.)
- `series_step1`, `series_step1_real`: the same for the series. If `ρ` is rational of period
  `N` (`8 ∣ N`) and `∑ ρ(k) 2^(-⌊k/2⌋)/k` is an algebraic multiple of `π`, the conclusion
  holds for its coefficients `d_r`.
- `new_formula_step1`: the new 7/24 formula as an instance.

Proved without Baker:
- `series_eq_logs`, the setting of Part III:
  `∑ ρ(k) 2^(-⌊k/2⌋)/k = ∑_{r^N = 1} d_r Log(1 - r/t)`, with `d` the finite Fourier
  transform of `ρ(k) t^(k mod 2) i^⌊k/2⌋` (`fourier_inversion`, `twist_mul`).
- `log_form`: a relation in logarithmic form, `∑ e_j Log w_j ∈ ℚ · iπ`.
- `step1_converse`: every combination of the 13 relations with algebraic coefficients gives
  an algebraic multiple of `π`.

**M7, part 1: the bounds of Theorem C** (`TheoremC.lean`), from `BakerTheorem`.
`algSpace N` is the space of rational patterns of period `N` whose series is an algebraic
multiple of `π`, and `ratSpace N` the subspace where the multiple is rational. Both are
`ℚ`-subspaces of `ℕ → ℚ`. For `N` a multiple of 120 (`theoremC_bounds`):
- every pattern of `algSpace N` has period 120 (`period_120`, for any `N` with `8 ∣ N`);
- `algSpace N` has dimension at most 13 (`rank_algSpace_le`, `finrank_algSpace_le`);
- `ratSpace N` has dimension at least 8 (`le_rank_ratSpace`, the eight series of
  `VSeries.lean`, no Baker) and at most 13.

The upper bound: the coefficient vectors of 14 patterns lie in `ℂ^13`, so they are
dependent over `ℂ`; Fourier inversion (`twist_eq_sum`) carries the dependence to the
patterns; and a complex dependence among rational vectors gives a rational one
(`rat_dependence`, by a `ℚ`-linear form `ℂ → ℚ`).

**M7, part 2: the rational part of Theorem C** (`GaloisValue.lean`, `ExactArgs.lean`,
`LogForms.lean`, `TheoremC2.lean`), from `BakerTheorem`. For `N` a multiple of 120:
- `finrank_ratSpace`: the rational patterns of period `N` whose series is a rational
  multiple of `π` form a space of dimension **exactly 8**;
- `span_namedFam`: every such pattern is a rational combination of the eight named series
  of `VSeries.lean`.

How the upper bound 8 is proved:
1. **Rational values are Galois invariant** (`conj_value`). The coefficients `d_r` of a
   rational pattern lie in `K = ℚ(ζ_120)`. Baker's descent, done over `K`
   (`baker_descent` for a subfield), writes the relation `∑ d_r Log(1 - r/t) = qπ` as a
   combination of integer relations with coefficients in `K`. An embedding `σ` of `K`
   with `σ(ζ) = ζ^b`, `b ≡ 1 (mod 4)`, applied to those coefficients gives again a relation
   (`conj_relation`), and `σ(d(ζ^a)) = d(ζ^(ba))` because the pattern is rational. So
   `∑_a d(ζ^(ba)) Log w_a = qπ` for every such `b`.
2. **Exact arguments** (`garg_table`). Each of the 24 arguments `arg w_j` is an explicit
   rational combination of `π`, `arg w_60` and `arg w_5`. Inputs: `arg w_0 = π/4`,
   `|arg w_j| ≤ π/4`, the symmetry `arg w_{30-j} = -arg w_j`, four signs, and eight of the
   13 relations, each of which fixes its argument sum up to a multiple of `2π` that the
   bounds decide (`argsum_of_prod`, `pin`).
3. **Exact logarithmic forms** (`log_exact`, `LogForms.lean`). For
   `b ∈ {1, 41, 49, 61, 73, 97}` and each of the 13 relations, the conjugated relation has
   `∑_j rel_l(bj) Log w_j = ν · iπ` with an explicit rational `ν`. The 78 values are
   computed by the kernel (`decide +kernel`); the file is generated by `scripts/logforms.py`.
4. **Five constraints** (`coeff_mem_constraintSpace`). Comparing `b = 41, 49, 61, 73, 97`
   with `b = 1` gives `c_11 = c_5 - c_4 + c_10`, `c_12 = 2 c_10`, `c_6 = c_7 = c_8 = c_9`
   for the coefficient vector `c ∈ ℂ^13`. That subspace has dimension 8
   (`finrank_constraintSpace_le`), so nine patterns are dependent (`dependent_of_coeffs`).

This also settles the exact multiples of `iπ` of the 13 relations (the case `b = 1`,
`lf_1_1` to `lf_1_13`): `-1/2, -1/2, -1/2, -1/2, 1/3, -5/6, -11/10, -39/10, -7/10, 17/10,
-4/3, -1/6, 1/4`, as in the docstrings of `Relations.lean`.

**M7, part 3: dimension exactly 13** (`FiveSeries.lean`, `TheoremC3.lean`). Five more
rational patterns of period 120, each an arctangent-type series `∑_j e_j arg w_j` with real
coefficients `e_j ∈ ℚ(ζ_120)` that are conjugate under `ζ ↦ ζ^b` (`b ≡ 1 mod 4`):

| pattern | value | coefficients | roots |
|---|---|---|---|
| `extraS3` | `-π/√3` | `±√3` | order 6 |
| `extraS2` | `-√2 π` | `±√2` | orders 8 and 24 |
| `extraS5` | `-√5 π` | `±√5` | orders 10 and 20 |
| `extraT1` | `(θ₁ - 3θ₃) π/5` | `±θ₁, ±θ₃` with `θ₁ = 2cos(π/10)`, `θ₃ = 2cos(3π/10)` | orders 10 and 20 |
| `extraT2` | `(3θ₁ + θ₃) π/5` | the same, conjugated | orders 10 and 20 |

For each: the power sum `∑_j e_j ζ^(jk)` equals a table of Gaussian integers (one
certificate per residue of `k`, modulo `Φ_24` or `Φ_20`); so the pattern is rational and
its series is `∑_j e_j arg w_j` (`hasSum_rhoA_of_lsum`); and `garg_table`'s exact arguments
give the value. None of this uses Baker's theorem.

- `fam13_linearIndependent` (no Baker): the eight named patterns and these five are
  linearly independent (values at thirteen positions, inverse matrix).
- `finrank_algSpace` (from `BakerTheorem`): `dim algSpace N = 13` for every `N` divisible
  by 120. `span_algFam`, `exists_coords13`: the thirteen patterns span.
- `theoremC` (from `BakerTheorem`): Theorem C in full. Period 120, dimension 13, and
  dimension 8 for the rational multiples.

The script `five_series_check.py` in `python/` checks the five series to 40
digits and the independence exactly, independently of Lean.

**M8: Theorem D and Bailey's table** (`TheoremD.lean`, `Bailey.lean`), from
`BakerTheorem`. By `span_namedFam` a rational pattern whose series is a rational multiple
of `π` is a combination `namedComb q` of the eight named patterns, with value
`(q 0 + q 2) π/4`. Everything below is linear algebra on `q`, with certificates found by
`scripts/baileygen.py` and checked by `linear_combination` and `decide +kernel`.

- `value_formula`: for `ρ ∈ ratSpace N` (`120 ∣ N`),
  `∑ ρ(k) 2^(-⌊k/2⌋)/k = (7ρ(1)/12 + ρ(2)/8 + ρ(3)/6 - 7ρ(7)/12 + ρ(9)/6 - ρ(14)/8) · π/4`.
  The multiple of `π` is read off from six terms.
- `theoremD`: if `ρ ∈ ratSpace N` has no term at `gcd(k, 120) < 4`, its series is 0.
  `exists_slow_term` is the contrapositive: a formula for a non-zero rational multiple of
  `π` has a non-zero term at some `k` with `gcd(k, 120) ≤ 3`.
- `zeroSpace_gcd`: for every `n ≥ 1`, a rational pattern of period `n` whose series is 0
  has period `gcd(n, 120)`.
- `finrank_zeroSpace`: for every `n ≥ 1` the zero relations of period `n` form a space of
  dimension `zeroCount (gcd n 120)`: `1, 1, 5, 3, 1, 7` at `8, 12, 24, 40, 60, 120` and `0`
  at the other ten divisors of 120. The bases are explicit: `namedL8` at 8;
  `namedL24 - namedL8` at 12 and 60; `namedA6, namedL6, namedL8, namedL24, namedTW` at 24;
  `namedA10 - namedA1, namedL8, namedL10` at 40; all seven at 120.
- `finrank_zeroSpaceEven`: with support on even `k`, exactly one zero relation when
  `12 ∣ gcd(n, 120)`, namely `namedL24 - namedL8`.
- `bailey_F2`, `bailey_F1`: the 27 counts of Bailey's Table 1 (binary, degree 1), as
  dimensions of these spaces: 17 rows with `n = 2B` and 10 rows with `n = B`.
- `theoremD_sharp`, `fast_eq`, `finrank_fast` (`SharpD.lean`): a pattern of `ratSpace N`
  with no term at `gcd(k, 120) < 4` is a multiple of
  `zD = -2·namedL8 + 2·namedL10 + namedL24`. These patterns form a space of dimension 1,
  and it is a zero relation. `zD` has no term at `gcd(k, 120) < 5` and has one at `k = 5`.
  The certificate (`coords_Dall`) uses the positions `k = 1, 2, 3, 7, 9, 11, 14` only.
- `theoremD_best_possible` (no Baker): for each two of the classes `gcd(k, 120) = 1, 2, 3`
  there is a formula with no term in those two: `namedA10 - 2·namedA6` (`π/4`, avoids 1
  and 2), `2·namedA1 - namedA10` (`π/4`, avoids 1 and 3), `6·namedA1 + 4·namedA6 + namedA10`
  (`7π/4`, avoids 2 and 3).

**Theorem D for algebraic multiples** (`TheoremDAlg.lean`, from `BakerTheorem`), as the
note states it: a pattern of `algSpace N` with no term at `gcd(k, 120) < 4` is a multiple
of `zD` (`theoremD_alg_sharp`), so its value is 0 (`theoremD_alg`); a formula for a
non-zero algebraic multiple of `π` has a term at some `k` with `gcd(k, 120) ≤ 3`
(`exists_slow_term_alg`).

**Bailey's sums themselves** (`BaileySums.lean`). `baileyZero B n` is the space of
coefficient vectors `A` with `P(1, 2^B, n, A) = ∑_j 2^(-Bj) ∑_{i=1}^n a_i/(nj + i) = 0`,
written as Bailey's double sum. Without Baker's theorem:

- `hasSum_bailey_F2`: for `n = 2B` Bailey's sum is the series of the pattern
  `ρ(nj + i) = a_i 2^⌊i/2⌋` (`patF2`), so `baileyZero B (2B)` and `zeroSpace (2B)` have the
  same dimension (`finrank_baileyZero_F2`);
- `hasSum_bailey_F1`: for `n = B` it is the series of the pattern supported on even `k`
  with `ρ(2(nj + i)) = 2^(i+1) a_i` (`patF1`), so `baileyZero B B` and `zeroSpaceEven (2B)`
  have the same dimension (`finrank_baileyZero_F1`).

The proof groups a convergent series into blocks of `n` terms (`hasSum_blocks_iff`). From
`BakerTheorem`:

- `bailey_count_F2`: for every `B ≥ 1`, `P(1, 2^B, 2B, ·)` has `zeroCount (gcd(2B, 120))`
  independent zero relations;
- `bailey_count_F1`: for every `B ≥ 1`, `P(1, 2^B, B, ·)` has one zero relation if `6 ∣ B`
  and none otherwise;
- `bailey_table`: the 27 rows of Bailey's Table 1, as triples `(B, n, count)`.

So Bailey's table is machine-checked in his own notation. The
script `value_formula_check.py` in `python/` recomputes the value formula, the
sharp form and the three examples exactly, independently of Lean.

**Theorem E: the optima** (`Classes.lean`, `PrimeMeasure.lean`, `FewestTerms.lean`,
`TheoremE.lean`), from `BakerTheorem`. For a series of the class F whose value is a non-zero
rational multiple of `π` (`theoremE`):

- `termCount_ge`: at least 40 of the 120 entries per period are non-zero, that is, at
  least `2/3` terms per bit (the cost of the classical BBP algorithm);
- `primeCost_ge`: the mean of `1/s` over the 32 classes of primes modulo 120 is at least
  `7/24` (the cost of the window algorithm).

Both are attained, without Baker: `huvent1_formula`, `huvent2_formula` are Huvent's two
formulas, stated in Bailey's notation `P(1, 2^12, 24, A)`, each with exactly 40 non-zero
entries; `primeCost_rhoNew` is `7/24` for the new formula. `cost_table` reproduces the table
of the note (Huvent 40 and 5/12, Euler 42 and 1/3, the new formula 55 and 7/24).

How it is proved. On paper the proof tries 6,724,520 cases (exact_optimum.py). In Lean:
- The 119 conditions `ρ(k) = 0` fall into 35 classes of proportional linear forms
  (`class_table`, checked by `decide +kernel`), and the 32 classes of primes into four types
  by `c mod 12` (`type_table`).
- `7/24`: a tree of 13 cases, written by hand (`prime_sum_ge`), on 17 linear facts.
- `40`: a branch-and-bound tree of 1,517 nodes with 2,229 derived facts, as a certificate
  (`theCert`) checked by a small verified checker (`checkCert`, `checkCert_sound`). The
  kernel evaluates the checker (`theCert_ok`, by `decide +kernel`, under a minute). No
  `native_decide`: only the three standard axioms.

**Theorem G: `log 23` has no binary BBP-type formula** (`Log23.lean`). An open question
of Bailey's compendium and of Chamberland (2003); Borwein, Borwein and Galway (2004) had
excluded the non-Aurifeuillian Machin-type formulas.

- `no_rel_23` (no Baker): if `∏ (1 - r/t)^(e_r) = ξ · 23^m` with `r`, `ξ` roots of unity,
  then `m = 0`. The private-prime argument of `Support.lean` is redone for relations up to
  a power of an integer `ℓ` (`coeff_eq_zero_upTo`, `support_upTo`); every root outside `R0`
  has a good prime of characteristic other than 23 (`goodPrimes_ne_23`: Lemma 3's primes
  are `≡ 1 mod 4`; Bang's primes have `ord_p(2) ≠ 11` except for the atom
  `Φ_11(2) = 23 · 89`, where 89 is taken); and for `r ∈ R0` no prime above 23 contains
  `t - r`, since `t^120 - r^120 = 2^60 - 1` is prime to 23 (`not_inP_R0`).
- `baker_no_log` (from `BakerTheorem`): Baker's descent with the extra logarithm `log ℓ`.
- `no_log23`: no series of the class F is a non-zero algebraic multiple of `log 23`.
  `bailey_no_log23_F2`, `bailey_no_log23_F1`: the same for `P(1, 2^B, 2B, A)` and
  `P(1, 2^B, B, A)`, every `B ≥ 1`.

Not covered: the binary families with `n` other than `B` and `2B` (Part IV of the note,
not formalized, and written for `π` only). `log23_probe.py` in `python/` is a
theory-free numerical search that agrees.

**Theorem H: the primes below 100** (`LogPrimes.lean`, `LogYes.lean`).

- `log_primes_below_100` (from `BakerTheorem`): for a prime `p < 100`, `log p` is the value
  of a series `∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational and periodic (`IsFValue`) if and only
  if `p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73}`.
- `isFValue_log_of_mem` (no Baker): the fifteen primes. One family gives all of them: the
  roots of `X^n = c` (`c` a unit of `ℤ[i]`) give the value
  `(1/2) log N(t^n - c) - (n/2) log 2` (`isFValue_gen`), and the fifteen primes are reached
  by products and quotients of the norms `N(t^n - c)`, each checked by `decide`.
- `not_isFValue_log_of_mem` (from `BakerTheorem`): the ten primes
  `23, 47, 53, 59, 67, 71, 79, 83, 89, 97`. `not_isFValue_log` is the general statement:
  it needs `ℓ` odd, prime to `2^60 - 1`, and a good prime of characteristic other than `ℓ`
  for every root of unity outside `R0`. That last condition is `good_ℓ`: the only atoms
  where `ℓ` could be the private prime have index `ord_ℓ(2)`, and there a second prime
  factor is used (89 for 23, 178481 for 47, 157 for 53, and so on).
- `isFValue_log_23_add_log_89`: `log 23 + log 89` is a value, although neither summand is.

A criterion for all positive rationals at once is Theorem K below (`LogConverse.lean`,
`LogExplicit.lean`), with the finite test that decides it for a prime (`LogPrimeTest.lean`).

**Theorem I: `arctan (2/7)` has no binary BBP-type formula** (`Arctan.lean`). Bailey's
compendium says it is not known whether `arctan (2/7)` possesses a binary BBP formula.

- `no_rel_gaussian` (no Baker): let `a`, `b` be algebraic integers with `a b = ℓ`, an odd
  prime to which `no_rel_of_goodPrimes` applies, and `a + b` an integer prime to `ℓ`. If
  `∏ (1 - r/t)^(e_r) = ξ (a/b)^m` with `r`, `ξ` roots of unity, then `m = 0`. This is
  `Log23.lean` redone for a quotient (`IsRelUpToQ`): a good prime of characteristic other
  than `ℓ` contains neither `a` nor `b`, and a prime above `ℓ` contains exactly one of them.
- `baker_no_extra` (from `BakerTheorem`): Baker's descent with one more logarithm `Λ`,
  `exp Λ = a / b`. `exp_two_arctan`: `exp (2i arctan (y/x)) = (x + yi)/(x - yi)`.
- `not_isFValue_arctan`, `no_arctan_of_goodPrimes`: `arctan (y/x)` is not a value of the
  class F when `x² + y² = ℓ` is such a prime. With `good_53`, `good_89`, `good_97`:
  `arctan (2/7)`, `arctan (5/8)`, `arctan (4/9)`, and the Bailey forms for `arctan (2/7)`.
- The positive half, no Baker: `exp_gamma` (`exp (i γ(O))` is a positive multiple of
  `z_O / t^|O|`), `isFValue_arctan_inv_129` (the thirteenth roots of unity give
  `arctan (1/129)`), `isFValue_arctan_two_sevenths_add`:
  `arctan (2/7) + arctan (6/11) = π/4 - arctan (1/129)` is a value.

`python/arctan_probe.py` is a theory-free numerical search that agrees.

**Theorem J: the cheapest checked computation** (`CheckedPair.lean`). Takahashi (2020)
computes `π` with one formula and checks it with a second one that shares most of its series.

- `pairCost ρ₁ ρ₂`: per period of 120, one for each position where one of the two patterns
  has a term, and one more where both have the same non-zero term (that series has to be
  computed twice). `pairCost_eq_zCost`: with `z = ρ₁ - ρ₂` this is (terms of `z`) + 2 (terms
  of `ρ₁` where `z` vanishes).
- `pairCost_ge` (from `BakerTheorem`): `60 ≤ pairCost ρ₁ ρ₂` for two different patterns of
  the class F with the same non-zero rational multiple of `π` as value.
- `pairCost_takahashi`: Takahashi's two formulas (`takahashi1_formula`,
  `takahashi2_formula`, both `P(1, 2^60, 120, A) = π`) have cost exactly 60.
  `pairCost_huvent`: Huvent's two formulas as a pair cost 65.
- The proof is a certificate as for Theorem E, on two patterns at once: `PCert`,
  `checkPair`, `checkPair_sound`, and the certificate `pairCert` (8,083 nodes on the zero
  relation, 180 on the formula, 17,953 derived facts), generated by `scripts/pairgen.py` and
  checked by `decide +kernel` (`pairCert_ok`, about four minutes). No `native_decide`.

Not proved: that Takahashi's pair is the only one at 60, and the bound 63 when no series
may be computed twice (both computed, `python/verify_pair_optimum.py`).

**Theorem K: which logarithms are values** (`LogCriterion.lean`, `LogConverse.lean`,
`LogExplicit.lean`). For a positive rational `y`, `log y` is a value of the class F exactly
when it is a rational combination of `log 2` and the numbers `log N((1+i)^n - c)`, and
exactly when a power of `y` is a product of integer powers of `2`, the numbers `2^m - 1`
and the two factors `2^n ∓ 2^((n+1)/2) + 1` of `4^n + 1`, `n` odd. Both halves are formal.

- `logSpan_le_fValues` (no Baker): every such combination is a value. `fValues` is the
  space of values. `isFValue_log_two_pow_sub_one`: `log (2^m - 1)`, every `m ≥ 1`;
  `isFValue_log_L`, `isFValue_log_M`: `log (2^n ∓ 2^((n+1)/2) + 1)`, every odd `n`.
- The converse, `mem_logSpan_of_isFValue_log` (from `BakerTheorem`), in `LogConverse.lean`.
  The steps:
  - `baker_no_extra` (from `Arctan.lean`) turns a formula for `log (a/b)` into a relation
    `IsRelUpToQ a b S e m` with `m ≠ 0`, and `cleared_upToQ` clears its denominators.
  - `aeval_pow_of_coprime`: an integer polynomial that vanishes at a primitive `N`-th root
    of unity `ζ` vanishes at `ζ^a` for `a` prime to `N`
    (`IsPrimitiveRoot.minpoly_eq_pow_coprime`). `cleared_conj`: so the cleared identity
    holds with every root of unity `r` replaced by `r^a`, for `a ≡ 1 (mod 4)`; this uses
    `i = ζ^(N/4)` (`zetaN_pow_quarter`). No field extension or norm map is needed.
  - `sum_log_coset_mem`: `∑_{c < L} log |t - u^c x|` is in `logSpan` when the `u^c x` are
    the roots of `X^M = x^M` with `(x^M)^4 = 1` (`IsPrimitiveRoot.nthRoots_eq`,
    `zO_nthRoots`). `sum_log_mod_four_mem`: the exponents in one class modulo 4.
    `sum_filter_coprime`: Möbius inversion over "prime to `N`" (`sum_moebius_dvd`).
    `sum_log_coprime_mem`: the sum of `log |t - r^a|` over the `a` prime to `N` with
    `a ≡ 1 (mod 4)` is in `logSpan`.
  - `log_sub_mem_logSpan_of_cleared`, the key lemma: from a cleared identity,
    `log c₁ - log c₂ ∈ logSpan`.
- `isFValue_log_iff`, `isFValue_log_nat_iff`, `isFValue_log_rat_iff`: the criterion with
  `logSpan`.
- `LogExplicit.lean` removes the Gaussian integers from the statement. `baseNumbers` is the
  set `{2} ∪ {2^m - 1} ∪ {2^(2j+1) ∓ 2^(j+1) + 1}`. `gaussian_unit_cases`, `tG_pow_even`,
  `norm_even_cases`, `norm_odd_cases` compute `N((1+i)^n - c)`; `logSpan_eq_baseSpan`;
  `log_mem_span_iff_pow` (a rational combination of logarithms of positive integers is a
  multiplicative identity for a power); and the criterion in elementary terms,
  `isFValue_log_rat_iff_pow`: `IsFValue (log y)` iff
  `∃ k > 0, ∃ n g e, (∀ i, g i ∈ baseNumbers) ∧ y ^ k = ∏ i, (g i : ℚ) ^ e i`.
  `isFValue_log_of_pow` is the "if" half, with no Baker.
- The finite test for a prime, in `LogPrimeTest.lean`. `primPart ℓ` is the primitive part
  that contains `ℓ`: `Φ_n(2)` with `n = orderOf (2 : ZMod ℓ)`, or for `n = 4d`, `d` odd, the
  one of `Aplus d = N(Φ_d(1+i))`, `Aminus d = N(Φ_d(-1-i))` that `ℓ` divides
  (`Aplus_mul_Aminus`: their product is `Φ_n(2)`).
  - `primPart_facts`: it divides `Φ_n(2)`, is positive, is divisible by `ℓ`, and its
    logarithm is a value of F (no Baker; `isFValue_log_cyclotomic_two`,
    `isFValue_log_Aplus`, `isFValue_log_Aminus`, by strong induction on `n` from
    `prod_cyclotomic_eq_X_pow_sub_one` and `prod_norm_eval_cyclotomic`).
  - `not_isFValue_log_of_partner` (from `BakerTheorem`): a prime `q ≠ ℓ`, `q ∤ n`, dividing
    `primPart ℓ` excludes `ℓ`. It supplies the three hypotheses of `goodPrimes_ne` in
    general: `q` has order `n` (`orderOf_two_of_not_dvd`, from Tau Ceti's
    `dvd_homogeneousCyclotomic_iff_orderOf_eq`); a prime of order `4 nOf (R k e)` divides
    the norm of the atom `R k e` (`dvd_norm_atom_R`); `ℓ` does not divide both `N(P k)` and
    `N(Q k)` (`not_dvd_norm_P_and_Q`, from `not_dvd_pair`).
  - `isFValue_log_prime_iff`, `isFValue_log_prime_iff_explicit` (odd `ℓ`,
    `Coprime (2^60 - 1) ℓ`): `IsFValue (log ℓ)` iff `primPart ℓ = ℓ^x`, or
    `primPart ℓ = ℓ^x * q` with `q` prime, `q ∣ n`, `IsFValue (log q)`. Uses
    `le_of_dvd_cyclotomic` (a prime of `Φ_n(2)` is at least every prime factor of `n`) and
    Tau Ceti's `multiplicity_homogeneousCyclotomic_eq_one`.
  - `isFValue_log_of_dvd`: the twelve primes dividing `2 (2^60 - 1)`;
    `isFValue_log_prime_classification`: every prime.
- Not formal: the statement (d) of the note about the other binary families. The list of 51
  primes below `10^7` is the test evaluated by `python/log_prime_criterion.py`; Lean proves
  the test, not each evaluation.
- `not_isFValue_log_38737`, `not_isFValue_log_433` (from `BakerTheorem`),
  `isFValue_log_433_add_log_38737` (no Baker): `Φ_72(2) = 433 · 38737` is the atom
  `R 4 0 = Φ_9(4i) = -4095 - 64i` (`atom_R40`), the only atom of index 72
  (`atoms_of_index_72`). The OEIS list A104885 contains 38737.

`python/log_prime_criterion.py` decides the criterion for any prime, and `python/log_probe.py`
is a theory-free numerical search for given primes and a given period.

**Baker's theorem is proved here too** (`Baker/`, `BakerBridge.lean`, `Unconditional.lean`).

- `Baker/` holds a formal proof of Baker's theorem by Michail Karatarakis (19 files, Apache
  License 2.0), fetched on 22 November 2026 and compiled here with three one-line
  adjustments. `Baker/README.md` gives the source, the checks made and every change.
- `bakerTheorem_of_linearIndependent` (`BakerBridge.lean`): Baker's theorem in the form a
  library states it (a finite family `l` with `LinearIndependent ℚ l`, algebraic
  coefficients) gives `BakerTheorem`.
- `bakerTheorem : BakerTheorem` (`Unconditional.lean`), from `Transcendental.baker`.
- `PiFormula.Unconditional.*`: Theorems C, D, E, G and H, the value formula and Bailey's
  counts, restated with no hypothesis. Each statement is the original with
  `(hB : BakerTheorem)` deleted (`scripts/unconditional_gen.py` writes the file), and each
  depends only on `propext`, `Classical.choice` and `Quot.sound`.

So the theorems exist in two forms. The files of Part III prove them from the hypothesis
`BakerTheorem` and use nothing outside Mathlib and Tau Ceti. `Unconditional.lean` removes
the hypothesis with the imported proof.

**Not proved for Theorem E:** that the optima are attained only by these formulas (two
formulas for `2/3`, two two-dimensional families for `7/24`), and the list of
non-dominated pairs. `theorem_e_experiment.py` shows the equality cases need trees of 20
and about 1,800 nodes.

## The size bound (how the last step was done)

`size_bound`: `A_n > n` and `A'_n > n` for odd `n ≥ 7`.

1. `N(z^n - 1) = ∏_{d ∣ n} N(Φ_d(z))` (`prod_norm_eval_cyclotomic`). Möbius inversion
   (`prod_eq_iff_prod_pow_moebius_eq_of_ne_zero`, in ℝ) gives
   `N(Φ_n(z)) = ∏_{ab = n} N(z^b - 1)^{μ(a)}` (`moebius_formula`).
2. For odd `b`, `N(z^b - 1)` is `L_b` or `M_b`, with `L_b M_b = 4^b + 1` and `M_b ≥ 2^b`.
   Each factor is therefore at least `2^{μ(a) b} 2^b / M_b` (`factor_bound`). Since
   `∑_{ab = n} μ(a) b = φ(n)`, this gives `A_n ∏_{d ∣ n} M_d ≥ 2^φ(n) ∏_{d ∣ n} 2^d`
   (`lower_bound`).
3. So `A_n > n` once `n ∏ M_d < 2^φ(n) ∏ 2^d` (`Crit`).
   - For odd `n ≥ 82` this follows from three facts: `∏_{d ∣ n} M_d ≤ 9 ∏_{d ∣ n} 2^d`
     (`prod_Mn_divisors_le`, by a telescoping invariant over all odd `b ≤ n`),
     `φ(n)² ≥ n` (`le_totient_sq`), and `9 s² < 2^s` for `s ≥ 10`.
   - The odd `n` from 7 to 81 are checked by `decide +kernel` (`crit_small`, about 20 s).

## Building

This folder is a Lake project (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`).
With Lean installed (elan):

```powershell
lake exe cache get      # once: download the compiled Mathlib
lake build              # build everything (the `Pilean` library)
lake build Pilean.PiFormula.Bridge   # one module
```

On Windows, Mathlib's deep folders can overflow the 260-character path limit when the
project sits in a long path; enabling long paths in Windows avoids that. `build.ps1` runs
the same build and prints only errors and the final line.

Toolchain: Lean 4.36.0, Mathlib v4.36.0.
