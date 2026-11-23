# Okada's criterion ("sum = 0 implies (a) and (b)"): plan of the Lean formalization

Date 2026-11-23. Goal: `theorem okadaOnlyIf : OkadaOnlyIf` (statement in `lean/Pilean/Erdos/Defs.lean`)
with no hypothesis. Files of this plan: `lean/Pilean/Erdos/Okada*.lean`.
Status line (keep current): see section 6.

Marks: [V] name checked by search in the local Mathlib (v4.36.0) or in the project; [N] checked
numerically or exactly with a program (section 5); [P] proved in Lean (axioms checked).

## 0. Is `OkadaOnlyIf` as stated true and provable from the paper proof?

Yes, as far as I can see. Points looked at:

- q = 1: `ZMod 1` is trivial, f = 0, `okadaG` is 0, no prime divides 1. Fine.
- The term n = 0 of `partialSum` is f(0)/0 = 0 in Lean, and n = q, 2q, ... carry f(0) = 0. Fine.
- `okadaC` sums over r = 1..q, so the residue 0 is represented by r = q and gets
  `lam q q p = v_p(q) + 1/(p-1)`; with f(0) = 0 this term is 0 anyway. (`lam q 0 p` would be wrong,
  but it is never used.)
- `CondA` asks `okadaG q f a = 0` for every a with `IsUnit a`; `okadaG` is defined on all of Z/q.
- None of the steps below needs "q odd" or "f(0) = 0": the whole "only if" direction holds for every
  q >= 1 and every rational f [N for the two limit formulas]. The propositions carry `Odd q` and
  `f 0 = 0` only because the glue has them (weaker statements; a worker may prove more).
- The paper proof (00_summary.md section 1, referee section 3) is correct; the route below replaces the
  digamma function, Gauss's formula and the Laurent expansion of the Hurwitz zeta function by two
  elementary limit formulas. The gaps G1 to G3 of the referee disappear or become explicit:
  G1 (no constant term) is `OkadaSumZero`; G2 (trivial character) is `OkadaHarmonicDiverges`;
  G3 (Baker and conjugation) is `OkadaBakerTwist`, done with `baker_descent` and `conj_relationF`.

## 1. The route

Notation: S_N(f) = sum_{1<=n<N} f(n)/n (`partialSum`); U = units of Z/q; f_h(n) = f(hn)
(`Okada.twistBy`); S'_N(u) = sum_{1<=n<N, gcd(n,q)=1} u(n)/n (`Okada.unitSum`); g = `okadaG q f` as a
function on ALL of Z/q, g(r) = sum_{m in M(q)} f(rm)/m; zeta = e^(2 pi i/q) = `ZMod.stdAddChar 1`;
fhat(a) = (1/q) sum_r f(r) zeta^(-ar) (`Okada.fourierCoeff`); P = primes dividing q;
layer_p = {r in Z/q : p | r, no other prime of P divides r} (`Okada.layer`),
l_p = sum_{r in layer_p} g(r) (`Okada.layerSum`).

First half (the sum stays 0 under twists):
 (W) window sums: sum_{N<=n<cN, n = r mod q} 1/n -> (log c)/q.                     `OkadaWindow`
 (S) S_N(f) -> 0 implies sum_r f(r) = 0 (from (W), c = 2).                          `OkadaSumZero`
 (F) sum_r f(r) = 0 implies S_N(f) -> - sum_{a != 0} fhat(a) Log(1 - zeta^a).       `OkadaFourierLimit`
 (B) sum_{a != 0} fhat(a) Log(1 - zeta^a) = 0 implies the same with fhat(ha),
     for every unit h (Baker, Galois group of Q(zeta)).                             `OkadaBakerTwist`
 => (T) S_N(f) -> 0 implies S_N(f_h) -> 0 for every unit h.                         `OkadaTwistInvariance`
Second half (reduction to the units):
 (R) S_N(f) - S'_N(g) -> -(1/q) sum_{p in P} l_p log p   (no condition on f).       `OkadaUnitReduction`
 (L) l_p = c_p (`okadaC`).                                                          `OkadaLayerSum`
 (H) S'_N(1) -> infinity (from (W)).                                                `OkadaHarmonicDiverges`
 (X) chi non-principal: sum_{n<N} chi(n)/n has a non-zero limit (L(1,chi) != 0).    `OkadaLOne`
 => (N) if S'_N(n -> u(hn)) -> c for all h in U (same c) then c = 0 and u = 0 on U. `OkadaUnitNonvanishing`
 (Q) logs of primes are linearly independent over Q.                                `OkadaLogPrimes`
Main deduction: (T), (R), (L), (N), (Q) => `OkadaOnlyIf`.
 Proof: S_N(f_h) -> 0; g of f_h is r -> g(hr), l_p of f_h is l_p of f (layer_p is stable under units);
 so S'_N(n -> g(hn)) -> (1/q) sum_p l_p log p for every h; by (N) this number is 0 and g = 0 on U: (a).
 Then sum_p c_p log p = 0 by (L), and (Q) gives c_p = 0: (b).

Why this route and not the one suggested (K1 to K5 with the constants gamma_a):
- No gamma_a, no digamma: (R) compares two partial sums directly, so the divergent parts cancel and
  no hypothesis sum f = 0 is needed in (R).
- No exchange of a limit with an infinite sum (no Tannery, no unique decomposition n = m k with
  m in M(q)): f = prod_{p in P} (1 - T_p/p) g with (T_p g)(r) = g(pr) is a FINITE identity, and it is
  already in the project (`Arith.serH_insert`, `ArithSeries.lean`). One prime at a time:
    sum_{n<N, n in A_m} h_m(n)/n - sum_{n<N, n in A_(m+p)} h_(m+p)(n)/n
        = - sum_{N<=n<pN, p|n, n in A_m} h_(m+p)(n)/n  ->  -(log p / q) sum_{r in A_m, p|r} h_(m+p)(r),
  where h_m = `Arith.serH q f m` and A_m = residues divisible by no prime of m. Only (W) is used.
- The coefficient of log p comes out as the layer sum l_p, which is visibly invariant under twists;
  l_p = c_p is a finite identity (L), proved with the existing `theta_insert` pattern.
- L(1,chi) enters only as "the partial sums of sum chi(n)/n converge to a non-zero number" (X); the
  link with Mathlib's `DirichletCharacter.LFunction` is Abel summation plus continuity at s = 1.

Earlier version of (R), discarded: limit -(1/q) D(f) with D(f) = sum_{m in M(q)} (log m/m) sum_{a in U}
f(am) [N: D(f) = sum_p c_p log p]. It needs Tannery and the decomposition n = m k; the layer form is
shorter.

## 2. The Lean objects (all compiled)

`OkadaDefs.lean` [P: compiles]: `Okada.twistBy`, `Okada.unitSum`, `Okada.layer`, `Okada.layerSum`,
`Okada.fourierCoeff`, `Okada.logForm`, and the propositions `OkadaWindow`, `OkadaSumZero`,
`OkadaHarmonicDiverges`, `OkadaFourierLimit`, `OkadaBakerTwist`, `OkadaTwistInvariance`,
`OkadaUnitReduction`, `OkadaLayerSum`, `OkadaLOne`, `OkadaUnitNonvanishing`, `OkadaLogPrimes`.
Glue (section 6 says which exist): `OkadaGlue.lean` (`okadaOnlyIf_of_main`), `OkadaGlueTwist.lean`
(`okadaTwistInvariance_of`), `OkadaGlueChar.lean` (`okadaUnitNonvanishing_of`),
`OkadaGlueWindow.lean` (`okadaSumZero_of_window`, `okadaHarmonicDiverges_of_window`),
`OkadaGlueAll.lean` (`okadaOnlyIf_of`: the seven leaves imply `OkadaOnlyIf`), `OkadaStatus.lean`
(what is proved so far: `okadaTwistInvariance`, `okadaOnlyIf_of_three`).
Final file, when all leaves are proved: `Okada.lean` with `theorem okadaOnlyIf : OkadaOnlyIf` and the
unconditional `erdos_pm_one`.

## 3. Work packages (leaves). All independent of each other.

State on 2026-11-23: WP1, WP2, WP3, WP7 are PROVED (section 6); WP4, WP5, WP6 are open.

Common rules: one file per package, namespace `PiFormula.Erdos` (helpers in `PiFormula.Erdos.Okada`),
import `Pilean.Erdos.OkadaDefs`, prove exactly the named proposition (`theorem okadaWindow :
OkadaWindow` etc.), no `sorry`, no new axioms.

### WP1 `OkadaWindow`  (file `OkadaWindow.lean`; about 150 lines; risk low)
Statement: for c >= 1 and r in Z/q, sum_{n in Ico N (cN), (n : ZMod q) = r} 1/n -> log c / q.
Proof A (recommended): for x >= q+1 real, (1/q)(log(x+q) - log x) <= 1/x <= (1/q)(log x - log(x-q))
(from `Real.add_one_le_exp` / `Real.log_le_sub_one_of_pos` [V: Mathlib/Analysis/SpecialFunctions/Log/
Basic.lean]); the n = r mod q in [N, cN) form an arithmetic progression of step q; the two bounds
telescope to (1/q) log(cN/N) + O(1/N). Squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`).
Proof B: all residues have the same limit (shift n -> n+1 changes the sum by O(1/N)) and the sum over
all residues is harmonic(cN-1) - harmonic(N-1) -> log c by `Real.tendsto_harmonic_sub_log` [V:
Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean].
Dependencies: none.

### WP2 `OkadaFourierLimit`  (file `OkadaFourier.lean`; about 300 lines; risk low to moderate)
Steps:
 1. For z in C with |z| = 1, z != 1: sum_{n<N} z^n/n -> -Log(1 - z).
    - convergence: Dirichlet's test `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` [V:
      Mathlib/Analysis/SpecificLimits/Normed.lean:930] with f n = 1/(n+1), z_n = z^(n+1) (shift by one:
      1/0 = 0 is not antitone), bound 2/|1-z| from `geom_sum_eq` [V: Mathlib/Algebra/Field/GeomSum.lean];
      then `cauchySeq_tendsto_of_complete` [V].
    - value: Abel's limit theorem `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt` [V:
      Mathlib/Analysis/Complex/AbelLimit.lean:248] with f n = z^n/n; for real x < 1,
      sum' n, z^n/n * x^n = -Log(1 - zx) by `Complex.hasSum_taylorSeries_neg_log` [V:
      Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean:280]; -Log(1 - zx) -> -Log(1 - z) by
      `Complex.continuousAt_clog` [V: .../Complex/Log.lean:269] (1 - z is in `Complex.slitPlane`
      because Re(1 - z) > 0); `tendsto_nhds_unique`.
 2. Finite Fourier inversion: f(n) = sum_a fhat(a) stdAddChar(a n). Either `ZMod.dft`, `ZMod.dft_dft`,
    `ZMod.invDFT_apply'` [V: Mathlib/Analysis/Fourier/ZMod.lean] (fourierCoeff q f a = (1/q) * dft f a
    up to the cast Q -> C), or orthogonality `AddChar.sum_mulShift` [V: Mathlib/NumberTheory/
    LegendreSymbol/AddCharacter.lean:257] with `ZMod.isPrimitive_stdAddChar` [V: Mathlib/Analysis/
    SpecialFunctions/Complex/CircleAddChar.lean:95]. The project also has `PiFormula.fourier_inversion`
    (`lean/Pilean/PiFormula/Fourier.lean`, for `zetaN N` and patterns on N).
 3. `ZMod.stdAddChar (a * n) = (ZMod.stdAddChar a)^n` (AddChar: `AddChar.map_nsmul_eq_pow` [V name used
    in CircleAddChar.lean]); `ZMod.stdAddChar a != 1` for a != 0 (`ZMod.injective_stdAddChar` [V]);
    norm 1 (`Circle.norm_coe` / `ZMod.stdAddChar_apply` [V]).
 4. Assemble: S_N(f) = sum_a fhat(a) sum_{n<N} (zeta^a)^n/n; the term a = 0 has fhat(0) = (1/q) sum f = 0.
Missing from Mathlib: the value of sum z^n/n on the unit circle (step 1). Dependencies: none.
A stronger form is true and may be proved instead: without sum f = 0,
S_N(f) - fhat(0) * harmonic(N-1) -> the same limit.

### WP3 `OkadaBakerTwist`  (file `OkadaBaker.lean`; about 250 lines; risk moderate, API only)
Imports: `Pilean.PiFormula.Unconditional` (`PiFormula.bakerTheorem : BakerTheorem` [V]),
`Pilean.BaseB.SubseriesAux` (`BaseB.extF`, `BaseB.extF_coe`, `BaseB.conj_relationF` [V]),
`Pilean.PiFormula.Baker` (`baker_descent` [V]). No use of `baker_galoisF`: that lemma wants i in the
field and a term q*pi; here the relation is homogeneous and the field is Q(zeta_q), q odd.
Steps:
 1. F := `IntermediateField.adjoin Q {zeta}`, zeta = `ZMod.stdAddChar (1 : ZMod q)` = exp(2 pi i/q)
    (`ZMod.stdAddChar_coe` [V]); primitive q-th root (`Complex.isPrimitiveRoot_exp` [V: Mathlib/
    RingTheory/RootsOfUnity/Complex.lean:92]); integral; every element of F is algebraic (copy
    `isAlgebraic_of_mem_K120`, `lean/Pilean/PiFormula/GaloisValue.lean:43`).
 2. For a unit h there is sigma : F ->a[Q] C with sigma(zeta) = zeta^(h.val): copy
    `exists_embedding` (`GaloisValue.lean:56`): `Polynomial.cyclotomic_eq_minpoly_rat` [V: Mathlib/
    RingTheory/Polynomial/Cyclotomic/Roots.lean:178], `IsPrimitiveRoot.pow_of_coprime` [V],
    `IsPrimitiveRoot.isRoot_cyclotomic` [V], `IntermediateField.algHomAdjoinIntegralEquiv` [V:
    Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:649], `ZMod.val_coe_unit_coprime` (check).
 3. T := univ.filter (a != 0); lam a := Log(1 - stdAddChar a); exp(lam a) = 1 - stdAddChar a is
    algebraic and non-zero for a != 0; beta a := fourierCoeff q f a on T, 0 outside; beta a in F.
    `baker_descent bakerTheorem F hF lam T hexp beta hbeta hbeta0 h : SpanIn F (IntRel T lam) beta`;
    `conj_relationF sigma hspan` gives sum_{a in T} extF sigma (beta a) * lam a = 0.
 4. extF sigma (fourierCoeff q f a) = fourierCoeff q f (h * a): `extF_coe`, `map_sum`, `map_mul`,
    `map_inv0`, `map_natCast`, `map_ratCast`, and sigma(zeta^j) = zeta^(h j).
Dependencies: none. Baker's theorem is used only here.

### WP4 `OkadaUnitReduction`, as `OkadaWindow -> OkadaUnitReduction`
(file `OkadaReduction.lean`; about 350 lines; risk moderate)
Imports `Pilean.Erdos.ArithSeries` (`Arith.serH`, `Arith.serH_insert`, `Arith.summable_serH`,
`Arith.dvd_of_dvd_prime_mul`; and the identity `serH q f q.primeFactors r = okadaG q f r`, proved
inline at `ArithSeries.lean:300`, via `Nat.mem_factoredNumbers_iff_primeFactors_subset` [V]).
Steps: for m a set of primes dividing q put A_m = {r : no prime of m divides r} and
R_m(N) = sum_{n<N, (n : ZMod q) in A_m} serH q f m n / n. Then R_empty = S_N(f) (`Arith.serH_empty`),
R_P = S'_N(g) (`ZMod.isUnit_iff_coprime` [V]; as at `ArithSeries.lean:293`).
 1. One prime (p not in m, H = serH q f (insert p m)):
    R_m(N) - R_(m+p)(N) = - sum_{N<=n<pN, p|n, n in A_m} H(n)/n   (exact, from `serH_insert` and the
    substitution n -> pn), which tends to -(log p/q) kappa(m,p), kappa(m,p) = sum_{r in A_m, p|r} H(r),
    by `OkadaWindow` (finite sum over residues).
 2. kappa(m,p) does not change when a further prime p'' (not in m, != p) is inserted in m and in H:
    the proof of `Arith.theta_insert` (`ArithSeries.lean:200`) with the weight w = indicator of p | r,
    which is "harmonic" at p'' (the p'' solutions r of p'' r = r' agree with r' on divisibility by
    p). `theta_insert` asks the weight condition at every prime; restate it for the inserted prime only.
    Hence kappa(m,p) = l_p for every m.
 3. Telescoping over an enumeration of P (`Finset.induction_on`).
Alternative for 1 to 3: inclusion-exclusion over subsets S of P: S_N(f) = sum_S (-1)^|S| sum_{n <
pi(S) N, pi(S) | n} g(n)/n.
Dependencies: WP1 only as a hypothesis (can start at once).

### WP5 `OkadaLayerSum`  (file `OkadaLayer.lean`; about 350 lines; risk moderate; pure algebra)
Statement: sum_{r in layer_p} okadaG q f r = okadaC q f p. [N: exact for 14 values of q]
Proof: (i) rewrite `okadaC` as sum over r in Z/q of f(r) w(r) with w(r) = lam q (if r = 0 then q else
r.val) p. (ii) w is harmonic at every prime p' != p of q: sum_{r : p' r = r'} w(r) = p' w(r') for
p' | r' (min(v_p(r), v_p(q)) is unchanged). So by the `theta_insert` pattern over the primes != p:
okadaC = sum_{r in A_(P-p)} serH q f (P-p) r * w r. (iii) last prime p, with serH (P-p) = g - T_p g/p:
sum_{r : p r = r'} w(r) is p(i-1) if v_p(r') = i < k and (p-1)(k-1) + k + 1/(p-1) if v_p(r') >= k
(k = v_p(q)), so w(r') - (1/p) sum_{pr = r'} w(r) = 1 for p | r', and w = 0 on the r prime to p.
Dependencies: none. Existing tools: `ArithSeries.lean`; `TheoremBAux.lean` has lemmas on `lam`.

### WP6 `OkadaLOne`  (file `OkadaLOne.lean`; about 350 lines; risk moderate to high: measure theory)
Statement: chi != 1 mod q: sum_{n<N} chi(n)/n -> L with L != 0. Take L = `DirichletCharacter.LFunction
chi 1`; `DirichletCharacter.LFunction_apply_one_ne_zero` [V: Mathlib/NumberTheory/LSeries/
Nonvanishing.lean:412].
Steps: A(t) = sum_{k in Icc 1 (floor t)} chi(k), |A| <= q (`MulChar.sum_eq_zero_of_ne_one` [V: Mathlib/
NumberTheory/MulChar/Basic.lean:612] on full periods).
 1. For real s > 1: LFunction chi s = LSeries chi s (`DirichletCharacter.LFunction_eq_LSeries` [V:
    .../LSeries/DirichletContinuation.lean:74]) = s * integral_{t>1} A(t) t^(-(s+1))
    (`LSeries_eq_mul_integral` [V: .../LSeries/SumCoeff.lean:137], r = 0;
    `LSeriesSummable_of_bounded_of_one_lt_re` [V: .../LSeries/Basic.lean:393]).
 2. s -> s * integral A(t) t^(-(s+1)) is right-continuous at s = 1: dominated by q t^(-2)
    (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence` [V], `integrableOn_Ioi_rpow_of_lt`
    [V: Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean:136]).
 3. LFunction chi is continuous at 1 (`DirichletCharacter.differentiable_LFunction` [V: ...
    DirichletContinuation.lean:97]). So LFunction chi 1 = integral_{t>1} A(t) t^(-2).
 4. sum_{k<=n} chi(k)/k -> integral_{t>1} A(t) t^(-2): `tendsto_sum_mul_atTop_nhds_one_sub_integral0`
    [V: Mathlib/NumberTheory/AbelSummation.lean:300] with f(t) = 1/t, c = chi (the boundary term
    A(n)/n -> 0).
Missing from Mathlib: the statement itself (the value of the conditionally convergent series at 1).
Dependencies: none.

### WP7 `OkadaLogPrimes`  (file `OkadaLogPrimes.lean`; about 100 lines; risk low)
Clear denominators (as `PiFormula.exists_int_relation`, `lean/Pilean/PiFormula/Baker.lean:104`), split
the integer exponents by sign, exponentiate: prod p^(a_p) = prod p^(b_p) in N with disjoint supports;
compare `Nat.factorization` (`Nat.factorization_prod` [V], `Nat.Prime.factorization_pow` [V]) or use
coprimality. `Real.log_injOn_pos` [V], `Real.log_prod` [V], `Real.log_pow`.

## 4. Glue packages (finite algebra and limits; no new mathematics)

- G1 `okadaOnlyIf_of_main` (`OkadaGlue.lean`) [P].
- G2 `okadaTwistInvariance_of : OkadaSumZero -> OkadaFourierLimit -> OkadaBakerTwist ->
  OkadaTwistInvariance` (`OkadaGlueTwist.lean`): fourierCoeff of f_h at a is fourierCoeff of f at
  h^(-1) a (reindex r -> h r); sum f_h = sum f; uniqueness of limits; back from C to R.
- G3 `okadaUnitNonvanishing_of : OkadaHarmonicDiverges -> OkadaLOne -> OkadaUnitNonvanishing`
  (`OkadaGlueChar.lean`): sum over h gives (sum_b u(b)) S'_N(1) -> phi(q) c, so sum_b u(b) = 0 and
  c = 0; for chi: sum_h chi(h) S'_N(u(h .)) = (sum_b chi(b) u(b)) sum_{n<N} chi^(-1)(n)/n, so
  sum_b chi(b) u(b) = 0 for chi != 1; orthogonality `DirichletCharacter.sum_char_inv_mul_char_eq` [V:
  Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean:82].
- G4 `okadaSumZero_of_window`, `okadaHarmonicDiverges_of_window` (`OkadaGlueWindow.lean`):
  S_(2N)(f) - S_N(f) = sum_r f(r) W_N(r) -> (log 2/q) sum_r f(r), and it tends to 0 when S_N converges;
  S'_(2N)(1) - S'_N(1) -> phi(q) log 2/q > 0 and S'_N(1) is monotone.
- G5 `okadaOnlyIf_of` (`OkadaGlueAll.lean`): the seven leaves imply `OkadaOnlyIf`.

## 5. Checks made before fixing the statements

Programs (scratch, not kept in the repository; the formulas are simple to redo with
`python/erdos_pm1_referee.py`):
- (R) in the earlier form and the equality D(f) = sum_p c_p log p: q = 1, 3, 9, 15, 21, 45, random
  rational f with f(0) = 0 and with f(0) != 0, sum f != 0: S_N(f) - S'_N(g) at N = 400000 agrees with
  -(1/q) sum_p c_p log p to 5e-6 (the error is O(1/N)).
- (L) l_p = c_p EXACTLY (rational arithmetic, g computed in closed form) for
  q = 1, 3, 5, 9, 15, 21, 25, 27, 45, 63, 75, 105, 135, 225, three random f each, with and without
  f(0) = 0. Also sum_{a in U} g(a) = sum_r f(r) exactly.
- (F): q = 3, 9, 15, 21, random f with sum 0: S_N(f) at N = 400000 against the logarithmic form: 7e-6.
- fourierCoeff of f_h at a = fourierCoeff of f at h^(-1) a: checked.

## 6. Status (update when something changes)

All files below compile (`lake build Pilean.Erdos.OkadaStatus`), no `sorry`, lines <= 100 characters,
axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` (checked 2026-11-23).

| item | file | state |
|---|---|---|
| definitions and the 11 propositions | `OkadaDefs.lean` | done |
| G1 `okadaOnlyIf_of_main` | `OkadaGlue.lean` | [P] |
| G2 `okadaTwistInvariance_of` | `OkadaGlueTwist.lean` | [P] |
| G3 `okadaUnitNonvanishing_of` | `OkadaGlueChar.lean` | [P] |
| G4 `okadaSumZero_of_window`, `okadaHarmonicDiverges_of_window` | `OkadaGlueWindow.lean` | [P] |
| G5 `okadaOnlyIf_of` (seven leaves) | `OkadaGlueAll.lean` | [P] |
| WP1 `okadaWindow` | `OkadaWindow.lean` | [P] |
| WP2 `okadaFourierLimit` | `OkadaFourier.lean` | [P] |
| WP3 `okadaBakerTwist` (Baker's theorem) | `OkadaBaker.lean` | [P] |
| WP7 `okadaLogPrimes` | `OkadaLogPrimes.lean` | [P] |
| `okadaSumZero`, `okadaHarmonicDiverges`, `okadaTwistInvariance`, `okadaOnlyIf_of_three` | `OkadaStatus.lean` | [P] |
| WP4 `OkadaUnitReduction` | `OkadaReduction.lean` | open |
| WP5 `OkadaLayerSum` | `OkadaLayer.lean` | open |
| WP6 `OkadaLOne` | `OkadaLOne.lean` | open |

The first half is complete with no hypothesis: `okadaTwistInvariance` (if sum f(n)/n = 0 then
sum f(hn)/n = 0 for every unit h; odd q, rational f, f(0) = 0).
`OkadaOnlyIf` now follows from three statements (`okadaOnlyIf_of_three`): WP4, WP5, WP6. They are
independent of each other and can be given to three agents at once. WP4 no longer needs `OkadaWindow`
as a hypothesis: `okadaWindow` is a theorem (import `Pilean.Erdos.OkadaWindow`).
When the three are proved: `Okada.lean` with
`theorem okadaOnlyIf : OkadaOnlyIf := okadaOnlyIf_of_three okadaUnitReduction okadaLayerSum okadaLOne`
and `erdos_pm_one` from `erdos_pm_one_of_okada` (`Main.lean`); then delete `OkadaStatus.lean`.

How WP2 and WP3 were done: as planned in section 3. WP2: `exists_limit_circle` (Dirichlet's test with
the weights 1/max(n,1)), `tendsto_circle_log` (Abel's limit theorem; note that `continuousAt_clog` is
in the root namespace), `fourier_inversion_zmod` (`AddChar.sum_mulShift`). WP3: `zetaQ`, `fieldQ`,
`exists_embedding_pow`, `coeffF` (the Fourier coefficient as an element of Q(zeta), so that an
embedding is applied with `map_sum`, `map_mul`, ... and no membership proofs), then `baker_descent`
and `BaseB.conj_relationF`. Reusable for WP6 if wanted: `Okada.tendsto_circle_log`.

How WP1 was done (differs from the two proofs proposed in section 3): z(n) = [n = r mod q] - 1/q has
partial sums bounded by 1 (`Nat.count_modEq_card` [V: Mathlib/Data/Int/CardIntervalMod.lean:143]), so
sum z(n)/n converges by Dirichlet's test, and log c <= sum_{N<=n<cN} 1/n <= log c + 1/(N-1) by
telescoping (`Finset.sum_Ico_sub` [V]).

Lean notes for the workers (met in this session):
- `simp only [hn]` with `hn : n.Coprime q` does not reduce `if n.Coprime q then _ else _` (the
  hypothesis is unfolded to `n.gcd q = 1`); use `have hn' : n.Coprime q = True := eq_true hn`.
- `if_pos`, `if_neg`, `if_true` are deprecated in this toolchain; use `simp only [h, reduceIte]`
  with the down-arrow prefix on `reduceIte`, as the other files of the project do.
- Renamed in this Mathlib: `tendsto_finsetSum` (not `tendsto_finset_sum`), `Finsupp.finsetSum_apply`,
  `tendsto_atTop_of_monotone` (the dichotomy "tends to infinity or converges").
- The set-builder notation for a filtered `range M` with the condition `(i : ZMod q) = r` elaborates
  `i` in `ZMod q`; write `((range M).filter fun i : Nat => (i : ZMod q) = r).card` (with the usual
  symbol for the natural numbers).
- Sums over the units: `Fintype.sum_equiv (Equiv.mulRight (ZMod.unitOfCoprime n hn))` with
  `ZMod.coe_unitOfCoprime`; over Z/q: `Fintype.sum_equiv (Units.mulLeft h)`.

**Update, 23 November 2026 (evening): complete.** WP4 (`okadaUnitReduction`, `OkadaReduction.lean`), WP5 (`okadaLayerSum`, `OkadaLayerAux.lean`, `OkadaLayer.lean`) and WP6 (`okadaLOne`, `OkadaLOne.lean`; by partial summation, without integrals) are proved. `okadaOnlyIf : OkadaOnlyIf` and the statements without hypothesis are in `Final.lean`.

## 7. Session log

2026-11-23, first session (design and start). Route fixed after numerical checks (section 5);
`OkadaDefs.lean` written; all five glue theorems proved; leaves WP1, WP2, WP3, WP7 proved (in this
order: WP7, WP1, WP3, WP2). Nothing was found wrong in `Defs.lean` or in the paper proof.
Not done: WP4, WP5, WP6 (sections 3 and 6). Sizes: 11 files, about 1430 lines.

Advice for the three open packages:
- WP5 is pure finite algebra and the safest; WP4 is the same machinery plus `okadaWindow`; both
  should start by restating `Arith.theta_insert` with the weight condition at the inserted prime only
  (its proof uses nothing else). They can share that lemma: put it in `OkadaTheta.lean` first.
- WP6 is the only one with measure theory. A possible way around the integrals: apply
  `Okada.tendsto_circle_log` to chi (finite Fourier expansion of chi, as in WP2, for complex-valued
  functions) to get the limit - sum_{a != 0} chihat(a) Log(1 - zeta^a); this proves convergence but
  not yet the equality with `DirichletCharacter.LFunction chi 1`, which still needs step 1 to 3 of
  WP6 (or Abel's theorem for Dirichlet series). So the integral route of section 3 stays the
  recommended one.
