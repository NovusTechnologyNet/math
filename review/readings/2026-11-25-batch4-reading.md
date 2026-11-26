# Independent reading, batch 4 (17 statements)

Source read: `view_batch4.txt` only, plus general Mathlib knowledge. No project files, no build.
Numerical checks were done with a short float script (in the scratchpad, `numcheck\c.py`), plus hand sums of the first few terms.

## Summary table

| Theorem | Plain statement (one sentence) | Confidence |
|---|---|---|
| `erdos_pm_one_of_cases` | Take q >= 2 that is even, or not a perfect square, or has prod_{p \| q} p/(p-1) <= 2. Then for every q-periodic f: N -> Z that is 0 on multiples of q and +-1 elsewhere, the partial sums of sum f(n)/n do not tend to 0. | high |
| `erdos_even_nat` | For even q >= 2 and such an f, the partial sums of sum f(n)/n do not converge to any real number. | high |
| `erdos_size_nat` | For q >= 2 with q/phi(q) = prod_{p \| q} p/(p-1) <= 2 (non-strict), the same conclusion as the first theorem. | high |
| `isSquare_of_condA_condB` | If q is odd (q = 1 allowed) and f: Z/q -> Q has f(0) = 0, f(r) an "odd rational" (odd numerator and odd denominator) for r != 0, and f satisfies the two Okada-type conditions CondA and CondB as defined, then q is a perfect square. | high on the text; medium on whether CondA/CondB are Okada's conditions |
| `not_cases_11025` | 11025 is odd, a square, and prod_{p \| 11025} p/(p-1) = 35/16 > 2, so the disjunction above fails. | high |
| `eq_zero_of_hasSum_mul_pi` | For coprime naturals 0 < q < p with (p,q) not in {(2,1),(3,1),(4,1),(3,2),(4,3)}, an N-periodic rho: N -> Q, and an algebraic real gamma: if sum_{k>=1} rho(k) (q/p)^{floor(k/2)} / k = gamma*pi (unconditionally), then rho is identically 0. | high |
| `pi_base_three_halves` | A 24-term-period series in powers of (2/3)^12 with the given rational coefficients sums to pi/4. | high; numerics match |
| `sqrt_three_pi_base_four_thirds` | A 12-term-period series in powers of (3/4)^6 with the given coefficients sums to sqrt(3)*pi/9. | high; numerics match |
| `hasSum_rhoFour` | sum_{k>=1} rho4(k) 4^{-floor(k/2)} / k = sqrt(3)*pi/9, rho4 a period-6 pattern (1/2, 1, 0, -1, -1/2, 0 for k = 1..6 mod 6). | high; numerics match |
| `formula_1` | The BBP formula: pi = sum_j 16^{-j} (4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6)). | high; numerics match |
| `formula_102_real` | For every real b with \|b\| > 1: log((b-1)/b) = -(1/b^2) sum_j b^{-2j} (b/(2j+1) + 1/(2j+2)). | high; numerics match (also for negative b) |
| `formula_93` | For every natural b >= 2: b^2 sqrt(3) arctan(sqrt(3)/(2b-1)) = (3/2) sum_j (-b^3)^{-j} (b/(3j+1) + 1/(3j+2)). | high; numerics match (b = 2, 3, 5) |
| `formula_88` | A combination of two arctangents involving the golden ratio phi and 5^{1/4} equals (1/(2*5^{13/4})) sum_j 5^{-5j} (125/(5j+1) - 25/(5j+2) + 5/(5j+3) - 1/(5j+4)). | medium: the exponents 1/4 and 13/4 must be real; see doubts |
| `formula_132` | 3 pi sqrt(phi) / 5^{5/4} = 2^{-9} sum_j ((2/phi)^10)^{-j} sum_{i<10} a_i/(10j+i+1), with the phi-power coefficients shown. | medium, same exponent issue |
| `formula_69` | pi sqrt(3) = (1/9) sum_j 3^{-6j} sum_{i<12} a_i/(12j+i+1), a = (81,-54,0,-9,0,-12,-3,-2,0,-1,0,0). | high; numerics match |
| `formula_p10_a` | The series sum_k (-1)^k/(2k+1)^2 is summable, and its sum is `catalanConst`, which is defined as that same sum. | high (almost tautological) |
| `formula_76` | pi^2 = (2/27) sum_j 3^{-6j} sum_{i<12} a_i/(12j+i+1)^2, a = (243,-405,0,-81,-27,-72,-9,-9,0,-5,1,0). | high; numerics match |

---

## General conventions used throughout

- **`HasSum f s`** (Mathlib) is unconditional summation over N. The net of finite partial sums over *all* finite subsets tends to s. For real series this is the same as absolute convergence with sum s. It is strictly stronger than convergence of the ordered partial sums. Every `formula_*`, `pi_base_*`, `sqrt_three_*`, `hasSum_rhoFour` and `eq_zero_of_hasSum_mul_pi` uses `HasSum`. Every Erdos statement uses `Filter.Tendsto (fun N => sum_{n in range N} ...) atTop (nhds _)`, i.e. ordinary ordered partial sums (conditional convergence). That is the right notion there, because the Erdos series are only conditionally convergent.
- **`Finset.range N` = {0, ..., N-1}.** So the Erdos partial sums include n = 0. That term is f(0)/0, and it is 0 twice over: f(0) = 0 (q divides 0) and x/0 = 0 in Lean. So it is harmless.
- **Bailey blocks.** Term j is sum_{i=0}^{N-1} a_i * (base factor)^j / (N j + i + 1), with j = 0, 1, 2, .... The pair (j, i) runs over the denominators k = Nj + i + 1 = 1, 2, 3, ..., each exactly once. No denominator is 0, so division by zero never occurs in these.
- **`BaileyFormula x c b B N a`** means: there is S with HasSum (block series) S and x = c * S. It is a plain identity "x = c * (series)" that also asserts unconditional summability. The same holds for the `Real`, `Int` and `Deg` variants. In `Deg` the denominator is raised to the power s.
- **`![a0, ..., a_{N-1}]`** is indexed by `Fin N` from 0. Entry i goes with the denominator Nj + i + 1.

---

## 1. `PiFormula.Erdos.erdos_pm_one_of_cases`

**Plain statement.** Let q be a natural number with q >= 2. Suppose
(q even) OR (q is not a perfect square in N) OR (prod_{p prime, p | q} p/(p-1) <= 2, computed in Q).
(Precedence: the three disjuncts together form the hypothesis. The arrow binds weaker than the disjunction.)
Then for every f: N -> Z with
- f(n+q) = f(n) for all n in N,
- f(n) = 0 whenever q | n,
- f(n) in {1, -1} whenever q does not divide n,

the sequence of partial sums s_N = sum_{n=0}^{N-1} f(n)/n (in R) does **not** tend to 0.

**Conventions.** The n = 0 term is 0, as above. The product is over `Nat.primeFactors q`, the set of distinct primes, and is q/phi(q). The denominators p - 1 are >= 1, so there is no division by zero. `IsSquare q` in N means q = r*r for some natural r.

**Edge cases and coverage.** q >= 2 rules out q = 0 and q = 1. The covered q are: all even q, all non-squares, and those odd squares whose radical satisfies prod p/(p-1) <= 2. An odd square fails this only if it has at least three distinct primes. Two odd primes give at most (3/2)(5/4) = 15/8 < 2. Odd squares that are covered include 9 (3/2), 225 (15/8), 441 (7/4), 1225 (35/24), and 3^2 7^2 11^2 (1.925). Odd squares that are **not** covered include 11025 = 105^2 (35/16), which is the smallest one, and 165^2 (2.0625). So the name "of_cases" is accurate. This is **not** the full Erdos conjecture for all q: odd squares with large q/phi(q) are left out, which `not_cases_11025` makes explicit. The hypotheses on f can be met for every q >= 2, so nothing is vacuous.

The conclusion is "does not tend to 0". It does not say the series converges. For non-square odd q with an unbalanced f the series diverges, and that case is also covered.

**What it does not say.** It does not cover odd squares with q/phi(q) > 2. It does not say the series converges to a nonzero limit. It says nothing about f taking values other than +-1.

**Doubts.** None about the text.

## 2. `PiFormula.Erdos.erdos_even_nat`

**Plain statement.** For q in N with q != 0 and q even (so q >= 2), and f as in §1, there is no real l with s_N -> l. In other words, the partial sums of sum f(n)/n diverge.

**Conventions.** Same as §1. The hypothesis is q != 0, and together with "even" this gives q >= 2.

**Edge cases.** Nothing is vacuous. This is stronger than "not tending to 0", and it is plausible: a period contains q - 1 non-multiples, an odd number, so sum_{r=1}^{q} f(r) is odd and hence nonzero, and the series then diverges like (sum f(r)/q) * log N.

**What it does not say.** Nothing about odd q.

**Doubts.** None.

## 3. `PiFormula.Erdos.erdos_size_nat`

**Plain statement.** For q >= 2 with sizeProd(q) := prod_{p prime, p | q} p/(p-1) <= 2 (in Q, **non-strict** <=), and f as in §1, the partial sums of sum f(n)/n do not tend to 0.

**The exact inequality.** sizeProd(q) = q/phi(q) <= 2. Equality holds exactly when q is a power of 2 (q = 2^a, a >= 1). Any even q with an odd prime factor has q/phi(q) >= 2 * 3/2 = 3 > 2. So the q covered are: powers of 2, and odd q with q/phi(q) <= 2 (for odd q the inequality is always strict). This includes odd squares such as 9, 225 and 441, but not 11025.

**Edge cases.** q = 1 is excluded. Without that, `primeFactors 1 = ∅`, the product is 1 <= 2, and f would have to be 0 everywhere, so the sums would tend to 0 and the statement would be false. The exclusion matters and is present.

**What it does not say.** It does not cover q with q/phi(q) > 2. It does not claim divergence.

**Doubts.** None.

## 4. `PiFormula.Erdos.isSquare_of_condA_condB`

**Plain statement.** Let q in N be odd (q = 1, 3, 5, ...). Let f: Z/qZ -> Q satisfy:
1. f(0) = 0;
2. for each residue r != 0, f(r) is an odd rational: writing f(r) = u/v in lowest terms with v > 0, both u (an integer) and v are odd. In particular f(r) != 0.
3. **CondA:** for every unit a of Z/qZ,
   G(a) := sum'_{m in M_q} f(a * (m mod q)) / m = 0 (in R),
   where M_q = { m in N : m != 0 and every prime factor of m divides q }. The sum is Mathlib's `tsum` over m in N, with the terms for m outside M_q set to 0.
4. **CondB:** for every prime p dividing q,
   C(p) := sum_{r=1}^{q} f(r mod q) * lambda(q,r,p) = 0 (in Q),
   where lambda(q,r,p) = v_p(r) if v_p(r) < v_p(q), and v_p(q) + 1/(p-1) otherwise (v_p = `padicValNat`).

Then q is a perfect square (q = s*s, s in N).

**Conventions.**
- `tsum` returns 0 for non-summable families, which could make CondA vacuous. It does not here: f is bounded (its domain is finite), and sum_{m in M_q} 1/m = prod_{p|q} p/(p-1) < infinity, so the family is absolutely summable and G(a) is a genuine sum.
- r = q in CondB contributes f(0) * ... = 0. `padicValNat p 0 = 0` is never used, since r >= 1.
- Units: for q = 1, Z/1 is the zero ring and 0 is a unit.

**Edge cases.**
- q = 1: Z/1 = {0}, so f = 0. Condition 2 is vacuous, CondA reduces to G(0) = f(0)/1 = 0, CondB is vacuous (no primes divide 1), and the conclusion IsSquare 1 is true. That is trivial but consistent.
- For q an odd prime or any odd non-square, the theorem says no f with odd-rational values satisfies both conditions.
- The hypotheses are not contradictory in general. For odd squares the theorem says nothing, since its conclusion is then true.

**What it does not say.** It does **not** mention the series sum f(n)/n at all. The link "CondA and CondB hold iff sum f(n)/n = 0" (Okada's theorem) is not part of this statement. Whether these definitions faithfully reproduce Okada's conditions has to be checked separately, by comparing with Okada's paper or with whatever theorem in the project connects them. The statement is also more general than +-1 values: any odd rationals are allowed.

**Doubts.** Are CondA and CondB exactly Okada's conditions? In particular, is the exceptional value v_p(q) + 1/(p-1) in lambda right, and is the range of a in CondA (units only) right? I can't decide this from the text. The theorem is only as strong as that correspondence.

## 5. `PiFormula.Erdos.not_cases_11025`

**Plain statement.** It is not the case that (11025 is even) OR (11025 is not a square) OR (prod_{p | 11025} p/(p-1) <= 2).

**Check.** 11025 = 3^2 5^2 7^2 = 105^2 is odd and a square. The product is (3/2)(5/4)(7/6) = 105/48 = 35/16 = 2.1875 > 2. True.

**Meaning.** The case split of §1 really excludes q = 11025, which is the smallest odd square it excludes (see §1). The statement says nothing about Erdos for q = 11025 itself.

## 6. `PiFormula.RatBase.TheoremR.eq_zero_of_hasSum_mul_pi`

**Plain statement.** Let p, q in N with 0 < q < p and gcd(p,q) = 1, and suppose (p,q) is not one of (2,1), (3,1), (4,1), (3,2), (4,3). Let N >= 1, let rho: N -> Q satisfy rho(k+N) = rho(k) for all k, and let gamma be a real number algebraic over Q. If
sum_{k>=0} rho(k) * (q/p)^{floor(k/2)} / k = gamma * pi
(HasSum, unconditional), then rho(k) = 0 for **every** k in N.

**Conventions.**
- **`k / 2` is natural-number division, i.e. floor(k/2).** The weight is (q/p)^{floor(k/2)}, not (q/p)^k and not (q/p)^{k/2}. The pairs k = 2m, 2m+1 share the factor (q/p)^m. So this is a series in "base sqrt(p/q)" with the odd-index terms carrying an extra factor sqrt(p/q) relative to the strict geometric weighting. Equivalently, it is sum c_k x^k / k with x = sqrt(q/p) and c_k = rho(k) for k even, rho(k)/x for k odd. Anyone reading "base p/q" should know this.
- k = 0 term: division by 0 gives 0. rho(0) is then pinned down only through periodicity, rho(0) = rho(N) = 0, so the conclusion "rho = 0" including rho(0) is still justified.
- gamma = 0 is allowed (0 is algebraic). So the statement includes "no nonzero periodic rho gives sum 0", a "no zero relation" claim, as well as "no formula for any algebraic multiple of pi".
- Summability is automatic because q/p < 1.

**Edge cases.** The excluded pairs are exactly those where the companion statements below exhibit nonzero formulas (4/1 via `hasSum_rhoFour`, 3/2 via `pi_base_three_halves`, 4/3 via `sqrt_three_...`), which is consistent. Pairs with q >= p are outside the statement (the series would diverge or the base would be <= 1). q = 0 is excluded. Nothing is vacuous: for instance (5,1) and (5,2) satisfy the hypotheses.

**What it does not say.** It does not cover rho with irrational or algebraic coefficients, polylog-type denominators k^s with s > 1, or constants other than algebraic multiples of pi. It also does not cover the strict weighting (q/p)^k unless that is rewritten with p, q replaced by p^2, q^2. The coprimality and the order condition would then still need to be checked.

**Doubts.** None about the text. The main thing to flag is the floor(k/2) convention.

## 7. `PiFormula.RatBase.pi_base_three_halves`

**Plain statement.**
pi/4 = sum_{j>=0} (2/3)^{12 j} sum_{i=0}^{23} a_i / (24 j + i + 1),
with a = (1/2, 1/3, 0, 0, 2/9, 8/27, 4/27, 0, 0, 16/243, 16/243, 0, -32/729, -64/2187, 0, 0, -128/6561, -512/19683, -256/19683, 0, 0, -1024/177147, -1024/177147, 0) (unconditional HasSum).

**Note.** `baileyBlockRat p q B N` uses the factor (q/p)^{B j} = (2/3)^{12 j}, a block of 24 denominators per power (2/3)^12. That is the floor(k/2) convention of §6 written in block form: a_i = rho(i+1) (2/3)^{floor((i+1)/2)}.

**Numerical check.** j = 0 by hand: 0.5 + 0.1667 + 0.0444 + 0.0494 + 0.0212 + 0.0066 + 0.0060 - 0.0034 - ... ≈ 0.785. The full sum is 0.7853981634, and pi/4 = 0.7853981634. **Matches.**

## 8. `PiFormula.RatBase.sqrt_three_pi_base_four_thirds`

**Plain statement.** sqrt(3) pi / 9 = sum_{j>=0} (3/4)^{6j} sum_{i=0}^{11} a_i/(12j+i+1), with a = (1/4, 3/8, 3/8, 9/32, 9/64, 0, -27/256, -81/512, -81/512, -243/2048, -243/4096, 0).

**Numerical check.** Sum = 0.6045997881, and sqrt(3) pi/9 = 0.6045997881. **Matches.**

## 9. `PiFormula.RatBase.hasSum_rhoFour`

**Plain statement.** sum_{k>=0} rho4(k) (1/4)^{floor(k/2)} / k = sqrt(3) pi / 9, where rho4(k) depends on k mod 6: 1 -> 1/2, 2 -> 1, 4 -> -1, 5 -> -1/2, and 0, 3 -> 0. The k = 0 term is 0, since rho4(0) = 0 and division by 0 also gives 0.

**Conventions.** `seriesTermRat 4 1`, so the weight is (1/4)^{floor(k/2)} (natural division). Read as a power series, it lives in x = 1/2: sum rho4(k) * 4^{-floor(k/2)} / k.

**Numerical check (hand).** 0.5 + 1*(1/4)/2 - (1/16)/4 - (1/2)(1/16)/5 + (1/2)(1/64)/7 + (1/256)/8 - ... = 0.5 + 0.125 - 0.015625 - 0.00625 + 0.001116 + 0.000488 ≈ 0.6047. The script gives 0.6045997881, equal to sqrt(3) pi/9. **Matches.**

## 10. `PiFormula.Compendium.formula_1`

**Plain statement.** pi = 1 * S, where S = sum_j 16^{-j} [4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6)] (HasSum). This is the BBP formula.

**Numerical check.** j = 0: 4 - 0.5 - 0.2 - 0.1667 = 3.1333. The full sum is 3.14159265. **Matches.**

## 11. `PiFormula.Compendium.formula_102_real`

**Plain statement.** For every real b with \|b\| > 1:
log((b-1)/b) = -(1/b^2) * S, with S = sum_{j>=0} (b^2)^{-j} [ b/(2j+1) + 1/(2j+2) ] (HasSum).

**Conventions.** `baileyBlockReal β N a j` uses β^j with j natural (`Monoid.npow`), so no fractional powers occur. β = b^2 > 1. Negative b is fine: b^2 > 0, and (b-1)/b > 0 for b < -1 as well as for b > 1, so `Real.log` takes a positive argument and no `log|x|` convention is triggered. Derivation: with x = 1/b, S = b^2 sum_{k>=1} x^k/k = -b^2 log(1-x), so the identity is log(1 - 1/b). Correct for all \|b\| > 1.

**Edge cases.** \|b\| <= 1 is excluded. At b = +-1 the series diverges, and b = 0 would be meaningless.

**Numerical check.** b = 1.5: both sides -1.09861. b = 3: -0.405465. b = -2: 0.405465 = log(3/2). b = -1.2: 0.606136. **Matches.**

## 12. `PiFormula.Compendium.formula_93`

**Plain statement.** For every natural b >= 2:
b^2 sqrt(3) arctan( sqrt(3)/(2b-1) ) = (3/2) * S, where S = sum_{j>=0} (-b^3)^{-j} [ b/(3j+1) + 1/(3j+2) ] (HasSum; the third coefficient is 0, so the 3j+3 term is absent).

**Conventions.** `baileyBlockInt` with β = -b^3 (an integer cast to R) and B = 1, so the factor is 1/(-b^3)^j, a natural power. The signs alternate, with no fractional powers. 2b - 1 is computed in R from the cast of b, so there is no natural-subtraction problem (and b >= 2 anyway).

**Edge cases.** b = 0 and b = 1 are excluded. At b = 1 the series has \|β\| = 1 and is not absolutely summable, so HasSum would fail. The exclusion is necessary.

**Numerical check.** b = 2 by hand: S ≈ 2.5 - 0.0875 + 0.006417 - 0.000568 + ... = 2.41840, and (3/2)S = 3.6276. LHS = 4 sqrt(3) * pi/6 = 3.6276. The script also gives b = 3: 5.198332 on both sides, and b = 5: 8.232680 on both sides. **Matches.**

## 13. `PiFormula.Compendium.formula_88`

**Plain statement (reading the exponents as real).** With phi = (1+sqrt5)/2:
(1/sqrt(phi)) arctan( 5^{1/4}/sqrt(phi) * (233 - 329 sqrt5)/5938 ) + sqrt(phi) arctan( 5^{1/4}/sqrt(phi) * (939 + 281 sqrt5)/5938 )
= 1/(2 * 5^{13/4}) * sum_j 5^{-5j} [125/(5j+1) - 25/(5j+2) + 5/(5j+3) - 1/(5j+4)].

**Conventions. This is critical.** The text prints `5 ^ (1 / 4)` and `5 ^ (13 / 4)` with no type ascription on the exponent. If the exponent were a natural number, 1/4 = 0 and 13/4 = 3, giving 5^{1/4} -> 1 and 5^{13/4} -> 125. The default elaboration of a bare numeral exponent in Lean/Mathlib is N, which is a well-known pitfall.

**Numerical check.**
- With real exponents (rpow): LHS = 0.3047378841 and RHS = 0.3047378841. **Matches.**
- With natural exponents (1 and 125): LHS = 0.20802 and RHS = 0.45569. **Does not match.**

So the statement is true only under the real-exponent reading. If it compiles with a proof, the exponents must be real, but the printed view cannot show that.

**What it does not say.** Nothing about the arctan expression being a "nice" constant. It is just the stated identity.

**Doubts.** Please confirm, for example with `set_option pp.numericTypes true` or by inspecting the source, that the exponents are `(1/4 : ℝ)` and `(13/4 : ℝ)`. If they were natural, the theorem would be false, so it could not have been proved. More likely the ascription was simply dropped by the printer.

## 14. `PiFormula.Compendium.formula_132`

**Plain statement.** 3 pi sqrt(phi) / 5^{5/4} = 2^{-9} * S, where S = sum_{j>=0} ((2/phi)^{10})^{-j} sum_{i=0}^{9} a_i/(10j+i+1), with real coefficients a = (256phi, 128phi^3, 64phi^4, 32phi^4, 0, -8phi^6, -4phi^8, -2phi^9, -phi^9, 0).

**Conventions.** β = (2/phi)^10 ≈ 8.33 > 1 (a natural power), and the coefficients are real (`BaileyFormulaReal`). The only possible problem is `5 ^ (5 / 4)` with an unascribed exponent. As a natural exponent, 5/4 = 1 would give 5.

**Numerical check.** S/512 = 1.6034389982. With real 5^{5/4}, the LHS is 1.6034389982: **matches**. With 5^1, the LHS would be 2.3977, which does not match. So the same doubt applies as in §13.

## 15. `PiFormula.Compendium.formula_69`

**Plain statement.** pi sqrt(3) = (1/9) sum_{j>=0} 3^{-6j} [81/(12j+1) - 54/(12j+2) - 9/(12j+4) - 12/(12j+6) - 3/(12j+7) - 2/(12j+8) - 1/(12j+10)].

**Numerical check.** j = 0: 5.44127, and the full sum is 5.4413981. pi sqrt3 = 5.4413981. **Matches.**

## 16. `PiFormula.Compendium.formula_p10_a`

**Plain statement.** HasSum (k ↦ (-1)^k/(2k+1)^2) catalanConst, where `catalanConst` is *defined* as sum'_k (-1)^k/(2k+1)^2.

**Vacuity.** HasSum f (tsum f) is equivalent to `Summable f`. So the whole content is "this series is (absolutely) summable", and its sum is the constant named catalanConst by definition. The theorem does not connect catalanConst to any other description of Catalan's constant (an integral, Mathlib's constant if one exists, or a BBP-type formula). Numerically, the sum is 0.9159656, which is Catalan's constant, so the definition is the right one.

**What it does not say.** No identity. It is only summability plus a definitional unfolding.

## 17. `PiFormula.Compendium.formula_76`

**Plain statement.** pi^2 = (2/27) S, where S = sum_{j>=0} 3^{-6j} sum_{i=0}^{11} a_i/(12j+i+1)^2, with a = (243, -405, 0, -81, -27, -72, -9, -9, 0, -5, 1, 0). The denominators are squared (s = 2).

**Numerical check.** (2/27) S = 9.8696044011, and pi^2 = 9.8696044011. **Matches.**

---

## Main points for the authors

1. **Unascribed fractional exponents in `formula_88` and `formula_132`** (`5 ^ (1/4)`, `5 ^ (13/4)`, `5 ^ (5/4)`). The identities hold numerically only if these are real powers. Read as natural powers (1/4 = 0, 13/4 = 3, 5/4 = 1), both are false. The printed view is ambiguous, so confirm the exponent type with `pp.numericTypes` and print it in the published statement.
2. **`isSquare_of_condA_condB` does not mention the series.** It is a statement about the conditions CondA and CondB as defined. Its value for Erdos depends entirely on CondA and CondB being equivalent to sum f(n)/n = 0, which this statement does not assert. The tsum in CondA is genuinely summable, so it is not vacuous for that reason. `erdos_pm_one_of_cases` misses exactly the odd squares with q/phi(q) > 2, the smallest being 11025. `erdos_size_nat` is non-strict q/phi(q) <= 2, which means powers of 2 plus odd q with q/phi(q) < 2.
3. **Theorem R uses (q/p)^{floor(k/2)}** (natural division), not (q/p)^k. It also covers gamma = 0, i.e. "no zero relation". `formula_p10_a` is tautological apart from summability. All other numerical checks match to at least 9 digits.
