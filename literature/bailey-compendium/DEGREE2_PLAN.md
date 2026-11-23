# Degree 2 of Bailey's Compendium: plan for the Lean proofs

Scope: the 18 formulas of degree 2 in `ledger.json` (ids p10.a, 29-39, 76-78, 123-125). All 17
that are series `P(2, b, n, A)` were re-checked numerically for this plan (60 digits; the ledger
has 90), and every dilogarithm identity quoted below was checked to 50 digits.

Notation: `Li2(z) = sum_{k >= 1} z^k / k^2` (|z| <= 1), `a = log 2`, `b = log 3`,
`G = sum_{k >= 0} (-1)^k / (2k+1)^2` (Catalan), `Cl2(t) = Im Li2(e^(it))` (Clausen).

## 0. Status (keep current)

| item | state (23 Nov 2026) |
|---|---|
| foundation `lean/Pilean/Polylog/` (7 files) | compiles, no `sorry`; details in section 6 |
| formulas proved in Lean (8 of 18) | p10.a, 29, 30, 31, 32, 33, 76, 77 |
| formulas not proved, no theorem stated (10) | 78 (needs Kummer's formula at `i/sqrt 3`); 36, 37, 39 (Kummer at `zeta_24`, `zeta_24^7`, Clausen triplication); 123, 124, 34, 35, 38 (relation 123: five-term relation, route open); 125 |
| work packages | A, B, C, D, E done; F started (Clausen function); G, H open |

## 1. How a degree-2 formula becomes a statement about Li2

`P(s, beta, n, A) = sum_{k >= 0} beta^(-k) sum_{j=1}^{n} a_j / (n k + j)^s`. With `m = n k + j`
and `x = beta^(-1/n)`: `beta^(-k) = x^m beta^(j/n)`, so

    P(s, beta, n, A) = sum_{m >= 1} c(m) x^m / m^s,   c(j) = a_j beta^(j/n),  c of period n.

(The regrouping lemma: a series `sum_m u(m) / m^s` with `u(m + n) = u(m) / beta` is
`P(s, beta, n, (u(1), ..., u(n)))`.) By the discrete Fourier transform
`c(m) = sum_r chat(r) zeta_n^(r m)`, so `P = sum_r chat(r) Li_s(zeta_n^r x)`: a combination of
polylogarithms at the `n` points `zeta_n^r beta^(-1/n)`. For rational `A` the coefficients pair
up (`chat(-r) = conj chat(r)`), so `P` is a real combination of real and imaginary parts.

Two shortcuts avoid complex points:

* a pattern supported on the multiples of `d` gives `Li_s(x^d) / d^s` (real point);
* duplication `Li_s(z) + Li_s(-z) = 2^(1-s) Li_s(z^2)` merges the points `z`, `-z`.

Bases: 16 with n = 8 and 2^12 with n = 24 have `x = 2^(-1/2)`; 64 with n = 6 has `x = 1/2`;
3^6 with n = 12 has `x = 3^(-1/2)`; 2^20 with n = 40 has `x = 2^(-1/2)`.

## 2. Dilogarithm facts needed

Functional equations (E = elementary, C = needs complex analysis):

| tag | statement | where valid | proof |
|---|---|---|---|
| DUP | `Li2(z^2) = 2 (Li2(z) + Li2(-z))` | closed unit disc | rearrangement of the series (E) |
| REFL-R | `Li2(x) + Li2(1-x) = pi^2/6 - log x log(1-x)` | `0 < x < 1` | derivative zero on (0,1), limit at 0 (E) |
| LAND-R | `Li2(x) + Li2(x/(x-1)) = -(1/2) log^2(1-x)` | `-1 <= x <= 1/2` | derivative zero, value at 0 (E) |
| REFL-C | the same as REFL-R for complex z | lens `|z| < 1, |1-z| < 1` | derivative zero on a convex open set (C) |
| LAND-C | the same as LAND-R for complex z | `|z| <= 1, Re z <= 1/2` | derivative zero on `|z| < 1, Re z < 1/2`, then continuity of Li2 on the closed disc (C) |
| DIST | `Li2(z^p) = p sum_{w^p = 1} Li2(w z)` | closed unit disc | rearrangement (E) |
| KUM | `Im Li2(r e^(it)) = w log r + (Cl2(2w) + Cl2(2t) - Cl2(2w + 2t))/2`, `w = -arg(1 - r e^(it))` | `0 < r < 1` | from LAND-C, inversion on the circle and REFL-C; or derivative in r (C) |
| FIVE | Abel's five-term relation | two variables | derivative in one variable (C) |

Values (each checked numerically):

| value | closed form | from |
|---|---|---|
| `Li2(1)` | `pi^2/6` | Mathlib `hasSum_zeta_two` |
| `Li2(-1)` | `-pi^2/12` | DUP at 1 |
| `Li2(1/2)` | `pi^2/12 - a^2/2` | REFL-R at 1/2 |
| `Li2(-1/2)` | `-Li2(1/3) - (b-a)^2/2` | LAND-R at -1/2 (no closed form; cancels) |
| `Li2(1/4)` | `2 Li2(1/2) + 2 Li2(-1/2)` | DUP |
| `Li2(-1/3)` | `-Li2(1/4) - (2a-b)^2/2` | LAND-R at -1/3 |
| `Li2(1/9)` | `2 Li2(1/3) + 2 Li2(-1/3)` `= 6 Li2(1/3) - pi^2/3 + b^2` | DUP, then the lines above |
| `Li2(-1/8)` | `-Li2(1/9) - (2b-3a)^2/2` | LAND-R at -1/8 |
| `Li2(1/64)` | `2 Li2(1/8) + 2 Li2(-1/8)` | DUP |
| ladder | `6 Li2(1/2) - 6 Li2(1/4) - 2 Li2(1/8) + Li2(1/64) = pi^2/6` | the seven lines above |
| `Re Li2((1+i)/2)` | `5 pi^2/96 - a^2/8` | REFL-C at `(1+i)/2` (`1 - z = conj z`) |
| `Im Li2((1+i)/2)` | `G - pi a/8` | LAND-C at `(1+i)/2` (`z/(z-1) = -i`), `Li2(-i) = -pi^2/48 - i G` |
| `Re Li2(e^(i pi/6)/sqrt 3)` | `5 pi^2/72 - b^2/8` | REFL-C (`1 - z = conj z`) |
| `Im Li2(e^(i pi/6)/sqrt 3)` | `(2/3) Cl2(pi/3) - pi b/12` | LAND-C (`z/(z-1) = e^(-2 pi i/3)`), `Cl2(2pi/3) = (2/3) Cl2(pi/3)` |
| `Re Li2(i/sqrt 3)` | `Li2(-1/3)/4` | DUP |
| `Im Li2(i/sqrt 3)` | `(5/6) Cl2(pi/3) - pi b/12` | KUM (t = pi/2, w = pi/6) |
| `Re Li2(zeta_6/2)` | `Li2(-1/2)/2 + pi^2/18 - a^2/4` | LAND-C (`z/(z-1) = -i/sqrt 3`, inside the disc) |
| `Im Li2(zeta_6/2)` | `(5/6) Cl2(pi/3) - pi a/6` | LAND-C and the line for `i/sqrt 3`, or KUM |
| `Im Li2(z1)`, `z1 = zeta_24/sqrt 2` | `-pi a/12 + (Cl2(pi/3) + Cl2(pi/6) - G)/2` | KUM (`1 - z1 = ((sqrt 3 - 1)/2) e^(-i pi/6)`) |
| `Im Li2(z7)`, `z7 = zeta_24^7/sqrt 2` | `-pi a/12 + (Cl2(pi/3) - Cl2(5pi/6) + G)/2` | KUM (`1 - z7 = ((sqrt 3 + 1)/2) e^(-i pi/6)`) |
| Clausen | `Cl2(pi/2) = G`, `Cl2(2pi/3) = (2/3) Cl2(pi/3)`, `Cl2(pi/6) + Cl2(5pi/6) = (4/3) G`, `Cl2(pi/6) - Cl2(5pi/6) = Cl2(pi/3)/2` | DIST on the unit circle (p = 2, 3) |
| `R17 = Re (Li2(z1) + Li2(z7))` | `(3/8) Li2(1/2) - (1/4) Re Li2(zeta_6/2) + Re Li2((1+i)/2) + (1/8) Li2(-1/2)` | this IS relation 123; route not found, see section 4 |

## 3. The 18 formulas

Difficulty: 1 = real dilogarithm only; 2 = one complex point with `1 - z = conj z` or a Landen
image on the unit circle; 3 = Clausen values and Kummer's formula; 4 = needs a two-variable
relation (route not settled); 5 = the same with 40th roots of unity.

| id | page | statement | reduces to | needs | difficulty |
|---|---|---|---|---|---|
| p10.a | 10 | `G = 1 - 1/3^2 + 1/5^2 - ...` | definition of G (Mathlib has no Catalan constant) | a definition; summability | 0 |
| 30 | 10 | `pi^2 = 9/8 P(2, 64, 6, (16,-24,-8,-6,1,0))` | `36 Li2(1/2) - 36 Li2(1/4) - 12 Li2(1/8) + 6 Li2(1/64)` | ladder (REFL-R, LAND-R, DUP) | 1 |
| 32 | 10 | `log^2 2 = 1/32 P(2, 64, 6, (64,-160,-56,-40,4,-1))` | `4 Li2(1/2) - 6 Li2(1/4) - 2 Li2(1/8) + Li2(1/64)` | ladder | 1 |
| 29 | 10 | `pi^2 = P(2, 16, 8, (16,-16,-8,-16,-4,-4,2,0))` | `32 Re Li2((1+i)/2) - 8 Li2(1/2)` | REFL-C at (1+i)/2 | 2 |
| 31 | 10 | `log^2 2 = 1/6 P(2, 16, 8, (16,-40,-8,-28,-4,-10,2,-3))` | `(32 Re Li2((1+i)/2) - 20 Li2(1/2))/6` | REFL-C at (1+i)/2 | 2 |
| 33 | 10 | `G - pi log 2/8 = 1/16 P(2, 16, 8, (8,8,4,0,-2,-2,-1,0))` | `Im Li2((1+i)/2)` | LAND-C to `-i`, `Li2(-i)` | 2 |
| 76 | 24 | `pi^2 = 2/27 P(2, 3^6, 12, ...)` | `-18 Li2(1/3) + 36 Re Li2(z0) + 9 Li2(-1/3)`, `z0 = e^(i pi/6)/sqrt 3` | REFL-C at z0; LAND-R at -1/2, -1/3; DUP | 2 |
| 77 | 24 | `log^2 3 = 1/3^6 P(2, 3^6, 12, ...)` | `-10 Li2(1/3) + 12 Re Li2(z0) + 5 Li2(-1/3)` | as 76 | 2 |
| 78 | 24 | `pi sqrt 3 log 3 = 2/27 P(2, 3^6, 12, ...)` | `sqrt 3 (48 Im Li2(i/sqrt 3) - 60 Im Li2(z0))` | LAND-C to `e^(-2 pi i/3)`, KUM at `i/sqrt 3`, Clausen p = 2 | 3 |
| 39 | 10 | `G = 3/2^12 P(2, 2^12, 24, ...)` | `3 (Im Li2(z7) - Im Li2(z1))` | KUM at z1, z7; Clausen p = 3 | 3 |
| 36 | 10 | `pi sqrt 3 log 2 = 9/2^10 P(2, 2^12, 24, ...)` | `sqrt 3 (12 (Im Li2(z1) + Im Li2(z7)) - 18 Im Li2(zeta_6/2))` | KUM at z1, z7, zeta_6/2; Clausen p = 2, 3 | 3 |
| 37 | 10 | `sqrt 3 Cl2(pi/3) = 9/(5 2^10) P(2, 2^12, 24, ...)` | `sqrt 3 (2.4 (Im Li2(z1) + Im Li2(z7)) - 2.4 Im Li2(zeta_6/2))` | as 36; needs a definition of `Cl2(pi/3)` | 3 |
| 123 | 31 | `0 = P(2, 2^12, 24, ...)` | the value of `R17` in section 2 | FIVE (or Kummer's two-variable equation) | 4 |
| 124 | 32 | `0 = P(2, 2^12, 24, ...)` | 124 + 11 x 123 is elementary (`Re Li2(zeta_6/2)`, `Re Li2((1+i)/2)`, `Li2(1/2)`, `Li2(-1/2)`) | 123, LAND-C at zeta_6/2 | 4 |
| 34 | 10 | `pi log 2 = 1/256 P(2, 2^12, 24, ...)` | the paper: 34 = 8 x (39 - 33) - 1/2^6 x 123 - 1/2^8 x 124. Real part: `56 Li2(1/2) - 112 R17 - 64 Re Li2(zeta_6/2) + 128 Re Li2((1+i)/2) + 32 Li2(-1/2)`; imaginary part: `24 (Im Li2(z7) - Im Li2(z1)) - 8 Im Li2((1+i)/2)` | 33 (done), 39, 123, 124 | 4 |
| 35 | 10 | `pi sqrt 3 log 2 = 1/128 P(2, 2^12, 24, ...)` | formula 36 minus 27/2^9 x 123 minus 9/2^10 x 124 (erratum 1 of `00_summary.md`: the paper prints plus) | 36, 123, 124 | 4 |
| 38 | 10 | `G = 1/2^10 P(2, 2^12, 24, ...)` | the paper: 38 = 39 + 5/2^11 x 123 + 1/2^12 x 124 | 39, 123, 124 | 4 |
| 125 | 32 | `0 = P(2, 2^20, 40, ...)` | real parts at `zeta_40^r/sqrt 2`, r = 1, 7, 9, 17, and at `(+-1+i)/2`, `1/2` | FIVE with fifth roots of unity; route not found | 5 |

Coefficients of the reductions (for a formula `x = c P`, the line gives `x`): `Re[r]`, `Im[r]`
mean the real and imaginary part of `Li2(zeta_n^r x)`.

    29  (n = 8):  -16 Re0 + 32 Re1 - 16 Re4
    31  (n = 8):  (-20 Re0 + 16 Re1 - 20 Re4)/3
    33  (n = 8):  Im1
    30  (n = 6):  -36 Re0 + 72 Re1 - 36 Re3
    32  (n = 6):  -8 Re0 + 12 Re1 - 6 Re3
    34  (n = 24): 112 Re0 - 112 Re1 - 24 Im1 - 128 Re2 + 128 Re3 - 8 Im3 + 128 Re6 - 112 Re7
                  + 24 Im7 - 128 Re10 + 112 Re12
    35  (n = 24): 198 Re0 - 180 Re1 + 12 sqrt3 Im1 - 252 Re2 - 36 sqrt3 Im2 + 216 Re3 + 252 Re6
                  - 180 Re7 + 12 sqrt3 Im7 - 252 Re10 + 36 sqrt3 Im10 + 198 Re12
    36  (n = 24): 12 sqrt3 (Im1 + Im7) - 36 sqrt3 (Im2 - Im10)
    37  (n = 24): 2.4 sqrt3 (Im1 + Im7) - 4.8 sqrt3 (Im2 - Im10)
    38  (n = 24): -2.5 Re0 + Re1 - 3 Im1 + 5 Re2 - 2 Re3 - 5 Re6 + Re7 + 3 Im7 + 5 Re10 - 2.5 Re12
    39  (n = 24): -3 Im1 + 3 Im7
    76  (n = 12): -36 Re0 + 36 Re1 + 36 Re3 - 36 Re6
    77  (n = 12): -20 Re0 + 12 Re1 + 20 Re3 - 20 Re6
    78  (n = 12): -60 sqrt3 Im1 + 48 sqrt3 Im3
    123 (n = 24): 3072 Re0 - 4096 Re1 - 2048 Re2 + 4096 Re3 + 2048 Re6 - 4096 Re7 - 2048 Re10
                  + 3072 Re12
    124 (n = 24): -40960 Re0 + 45056 Re1 + 40960 Re2 - 49152 Re3 - 40960 Re6 + 45056 Re7
                  + 40960 Re10 - 40960 Re12
    125 (n = 40): -3145728 Re0 + 5242880 (Re1 + Re7 + Re9 + Re17) - 9437184 Re5 - 5242880 Re15
                  - 3145728 Re20

With `x = 2^(-1/2)`, n = 24: `Re0 + Re12 = Li2(1/2)/2`, `Re6 = Li2(-1/2)/4`,
`Re2 + Re10 = Re Li2(zeta_6/2)/2`, `Im2 - Im10 = Im Li2(zeta_6/2)/2`, `Re3`, `Im3` belong to
`(1+i)/2`, and `Re1 + Re7 = R17`.

## 4. What is not settled

* **Relation 123** is the one new real-part value of base 2^12: it gives `R17`. With
  `z7 = i z1`, `1 - z1 = p`, `1/(1 - z7) = 2 conj p`, `p = ((sqrt 3 - 1)/2) e^(-i pi/6)`,
  reflection and inversion turn it into a statement about `Re (Li2(2p) - Li2(p))`; a
  single-variable equation that closes the argument was not found. Abel's five-term relation
  with `x = z1`, `y = z7` has `x y / ((1-x)(1-y)) = -1`, which is promising, but leaves
  `Li2(v) - Li2(-v)` with `v = ((sqrt 3 - 1)/2)(1 + i)`. To do before any Lean work: find the
  derivation on paper (Broadhurst's ladders; Lewin, "Structural properties of polylogarithms").
* **Relation 125** (base 2^20): the same question with 40th roots of unity.
* **Formula 37** needs a definition of `Cl2(pi/3)`; proposed: `(polylog 2 (exp (i pi/3))).im`,
  with the series `sum sin(k pi/3)/k^2` as a `HasSum` statement.

## 5. Order of work and work packages

Independent packages are marked (par); each lists its inputs.

| WP | content | inputs | difficulty | formulas | state |
|---|---|---|---|---|---|
| A | `Polylog/Defs`: series, summability, `HasSum` forms, real version, blocks `P(s, b, n, A)`, regrouping, DUP | Mathlib | easy | - | done |
| B | `Polylog/Dilog`: real Li2, derivative, REFL-R, LAND-R, `Li2(1/2)`, the ladder | A | easy | 30, 32 | done |
| C | complex Li2: derivative on the open disc (`hasDerivAt_tsum_of_isPreconnected`), continuity on the closed disc (`continuousOn_tsum`), REFL-C on the lens, LAND-C with the limit to the boundary | A | medium | - | done |
| D (par) | Catalan's constant, `Li2(i)`, `Li2(-1)`; values at `(1+i)/2` | C | medium | p10.a, 29, 31, 33 | done |
| E (par) | base 3 real parts: value at `e^(i pi/6)/sqrt 3`, `Li2(-1/3)`, `Li2(1/9)` | B, C | medium | 76, 77 | done |
| F1 (par) | Clausen function: DIST for p = 3 on the circle (`Cl2(3t) = 3 (Cl2(t) + Cl2(t + 2pi/3) + Cl2(t + 4pi/3))`, a rearrangement like `polylog_dup`), then `Cl2(pi/6) + Cl2(5pi/6) = (4/3) G`, `Cl2(pi/6) - Cl2(5pi/6) = Cl2(pi/3)/2` | `Polylog/Clausen` | easy | - | started: definition, series, `Cl2(pi/2) = G`, duplication, `Cl2(2pi/3)`, `Im Li2(z0)` are proved |
| F2 | Kummer's formula KUM for `Im Li2(r e^(it))`, `0 < r < 1`. Two routes: (i) derivative in `r`, which needs `Cl2' (x) = -log(2 sin(x/2))` on `(0, 2 pi)`; get it from `d/dt Im Li2(r e^(it)) = -log |1 - r e^(it)|` and the limit `r -> 1` (uniform on compact subsets); (ii) from FIVE with `y = conj x`. Only four instances are needed: `i/sqrt 3`, `zeta_6/2`, `z1`, `z7` | C, F1 | hard | 78, 39, 36, 37 | open |
| G | relation 123: find the derivation on paper first, then FIVE in Lean: prove Abel's relation `Li2(x/(1-y)) + Li2(y/(1-x)) - Li2(x) - Li2(y) - Li2(xy/((1-x)(1-y))) = log(1-x) log(1-y)` for small `x, y` by the derivative in `x` (the pattern of `hasDerivAt_landen_complex_aux`), then extend by continuity as in `polylog_two_landen` | C, F | hard, route open | 123, 124, 34, 35, 38 | open |
| H | relation 125 | G | hard, open | 125 | open |

Also open, small: the decimal value of G printed on page 10 (`0.9159655941...`) is not proved;
it would follow from formula 33 or 39 with an error bound for the tail of the series.

Mathlib declarations (names verified by search in Mathlib v4.36.0). Used by the files of
section 6: `hasSum_zeta_two`, `Real.hasSum_pow_div_log_of_abs_lt_one`,
`Complex.hasSum_taylorSeries_neg_log`, `hasDerivAt_tsum_of_isPreconnected`,
`continuousOn_tsum`, `IsOpen.is_const_of_deriv_eq_zero`, `Set.EqOn.of_subset_closure`,
`HasDerivAt.real_of_complex`, `HasDerivAt.clog`, `Complex.hasStrictDerivAt_log`,
`Complex.log_conj`, `Complex.log_inv`, `Real.summable_one_div_nat_pow`, `Complex.hasSum_re`,
`Complex.hasSum_im`, `Complex.ofReal_tsum`, `Function.Injective.hasSum_iff`,
`Real.arctan_one`, `Real.arctan_inv_sqrt_three`. Present but not needed so far (Abel's limit
theorem is replaced by the uniform convergence on the closed disc):
`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`,
`Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone`,
`Convex.is_const_of_fderivWithin_eq_zero`, `hasDerivAt_tsum`, `Real.continuous_mul_log`,
`Real.one_sub_inv_le_log_of_pos`.

## 6. Status of the Lean files

(Updated as files compile. A file listed here compiles without `sorry`.)

| file | content | state |
|---|---|---|
| `lean/Pilean/Polylog/Defs.lean` | `polylog`, `polylogReal`, summability (`summable_polylog_term`), `hasSum_polylog`, `hasSum_polylog_nat`, `hasSum_re_polylog_nat`, `hasSum_im_polylog_nat`, `polylog_ofReal`, `polylog_conj`, `polylogReal_two_one`, `hasSum_dvd`, `polylog_dup`; blocks `baileyBlockDeg`, `baileyBlockDegReal`, `HasBaileyValueDeg`, `BaileyFormulaDeg`; regrouping `hasSum_block_sums`, `hasSum_baileyBlockDegReal_of_quasiperiodic`, `hasSum_baileyBlockDegReal_of_periodic`, `hasBaileyValueDeg_of_quasiperiodic` | compiles |
| `lean/Pilean/Polylog/Deriv.lean` | `hasDerivAt_polylog_succ`, `polylog_one` (`Li_1 = -log(1-z)`), `hasDerivAt_dilog`, `continuousOn_polylog`, and the real versions | compiles |
| `lean/Pilean/Polylog/Dilog.lean` | real Li2: `polylogReal_two_landen` on [-1, 1/2], `polylogReal_two_neg_one`, `polylogReal_two_half`, `polylogReal_two_reflection` on (0,1), `dilog_ladder_two`, `dilog_ladder_three` | compiles |
| `lean/Pilean/Polylog/DilogComplex.lean` | `polylog_two_reflection` (lens), `polylog_two_landen` (`|z| <= 1`, `Re z <= 1/2`), `re_polylog_two_of_re_eq_half`, `im_polylog_two_of_re_eq_half` | compiles |
| `lean/Pilean/Polylog/Catalan.lean` | `catalanConst`, `hasSum_catalanConst`, `Li2(i)`, `Re` and `Im` of `Li2((1+i)/2)` | compiles |
| `lean/Pilean/Polylog/PointBase3.lean` | `pointThree = e^(i pi/6)/sqrt 3`, `Re Li2(pointThree)` | compiles |
| `lean/Pilean/Polylog/Clausen.lean` | `clausen`, `hasSum_clausen`, `clausen_pi_div_two`, `clausen_two_mul`, `clausen_two_pi_div_three`, `polylog_two_pointThree_im` | compiles |
| `lean/Pilean/Compendium/Degree2Defs.lean` | `baileyFormulaDeg_one_iff`: for `s = 1` the new statement form is `BaileyFormula` of the degree-1 files | compiles |
| `lean/Pilean/Compendium/Degree2Base64.lean` | `formula_30`, `formula_32` | compiles |
| `lean/Pilean/Compendium/Degree2Base16.lean` | `formula_p10_a`, `formula_29`, `formula_31`, `formula_33` | compiles |
| `lean/Pilean/Compendium/Degree2Base3.lean` | `formula_76`, `formula_77` | compiles |

Formulas proved: p10.a, 29, 30, 31, 32, 33, 76, 77, each stated as printed
(`BaileyFormulaDeg x c 2 b B N A`; vector, prefactor, base and length compared with
`ledger.json` by a script). Axioms of every `formula_N`: `propext`, `Classical.choice`,
`Quot.sound`. Build: `lake build Pilean.Polylog.Clausen Pilean.Compendium.Degree2Base64
Pilean.Compendium.Degree2Base16 Pilean.Compendium.Degree2Base3`, about 90 seconds for the ten
modules (each file imports all of Mathlib, 13 seconds per file).

Not done on purpose (existing files were not edited): the new modules are not imported by
`lean/Pilean.lean`; `ledger.json` and `LEAN_STATUS.md` do not yet record the eight theorems.

Notes for whoever continues:

* `formula_p10_a` says that the series of G converges to `Polylog.catalanConst`, which is
  defined as the sum of that series; the content is the convergence. The printed decimals are
  not proved.
* In this Mathlib `ContinuousOn.div` for complex functions runs into a `whnf` timeout; the
  variant for groups with zero (the name ends in a subscript zero) works; see the proof of
  `polylog_two_landen`.
* Never let the unifier see `HasDerivAt.comp` at a numeral point (`h.comp 0 hd`): it unfolds
  real arithmetic. Prove the derivative at a variable point and rewrite afterwards
  (`hasDerivAt_landen_aux`).
* A second proof of `arg z = arctan (Im z / Re z)` exists in `Base3/PiValue.lean`
  (`arg_eq_arctan`); the foundation has its own copy (`arg_eq_arctan_of_re_pos`) so as not to
  import the base-3 files.
