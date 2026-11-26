# Independent reading of batch 2 (fourteen statements)

I read only `view_batch2.txt` and, for Mathlib notions, the Mathlib sources. Where I state numbers (sums, supports, counts), I computed them myself from the printed definitions with a short throw-away Python computation (exact rationals for the coefficients, floating point for the series sums). Nothing was compiled.

## Summary table

| Theorem | Plain statement (one sentence) | Confidence |
|---|---|---|
| `PiFormula.theoremB` | For every finitely supported rational combination of the arguments of Φ_{2k+1}(1+i), Φ_{2k+1}(−1−i), Φ_{2k+1}(i·2^{2^{e+1}}), if it equals qπ with q rational, then only the four "exceptional" atoms carry weight, the weights on Q0 and Q2 cancel, and q = (c(P0)+c(Q1))/2. | high |
| `value_formula` | Every periodic rational ρ (some period N > 0) whose series Σ_{k≥1} ρ(k)/(2^{⌊k/2⌋}k) sums to a rational multiple of π sums to (7/12ρ₁+1/8ρ₂+1/6ρ₃−7/12ρ₇+1/6ρ₉−1/8ρ₁₄)·π/4. | high |
| `theoremD_sharp` | A periodic ρ with rational-multiple-of-π sum that vanishes at every k with gcd(k,120) ∈ {1,2,3} is a rational multiple (possibly 0) of the fixed sequence zD. | high |
| `bailey_table` | For each of 27 listed (B, n, d), the ℚ-space of a ∈ ℚⁿ with Σ_{j≥0} 2^{−Bj} Σ_{i<n} a_i/(nj+i+1) = 0 has dimension d. | high |
| `theoremE` | Every periodic ρ whose series sums to rπ with r ∈ ℚ, r ≠ 0, has at least 40 nonzero values among ρ(0),…,ρ(119), and primeCost ρ ≥ 7/24. | high (on what is counted) |
| `termCount_eq_forty_iff` | For such ρ, exactly 40 nonzero values among ρ(0..119) holds iff ρ is a nonzero rational multiple of rhoHuvent1 or of rhoHuvent2 (two base-4096, 24-slot formulas). | high |
| `no_log23` | No periodic rational ρ has series sum q·log 23 with q a nonzero real algebraic number. | high |
| `log_primes_below_100` | For a prime p < 100, log p is a series value of this kind iff p ∈ {2,3,5,7,11,13,17,19,29,31,37,41,43,61,73}. | high |
| `isFValue_log_rat_iff_pow` | For rational y > 0, log y is such a value iff some positive power y^k is a product of integer powers of "base numbers" 2, 2^m−1 (m ≥ 1), 2^{2k+1}∓2^{k+1}+1. | high |
| `isFValue_log_prime_classification` | For prime ℓ, log ℓ is such a value iff ℓ divides 2(2^60−1), or every prime q ≠ ℓ dividing a certain "primitive part" of 2^d−1 (d = ord_ℓ 2) divides d and itself has log q such a value. | medium (type of `orderOf 2` not printed) |
| `not_isFValue_arctan_two_sevenths` | arctan(2/7) is not the sum of any such series. | high |
| `pairCost_ge` | Two different periodic ρ₁ ≠ ρ₂, both summing to the same rπ (r ≠ 0), have pairCost ≥ 60, where pairCost = |supp₁ ∪ supp₂| + #{k: ρ₁(k) = ρ₂(k) ≠ 0}, all within k = 0..119. | high |
| `checkedPair` | The statement of `pairCost_ge`, plus: two explicit 120-slot base-2^60 sequences rhoTak1, rhoTak2 both sum to π and have pairCost exactly 60. | high |
| `not_isFValue_log_38737` | log 38737 is not the sum of any such series. | high |

## Common ingredients (used by most statements)

**The series.** `seriesTerm ρ k = (ρ k : ℝ) / 2^(k/2) / k`, with `k/2` natural-number division. So the series is

  S(ρ) = Σ_{k ≥ 1} ρ(k) / (2^{⌊k/2⌋} · k).

- At k = 0 the term is ρ(0)/1/0 = 0 by Lean's x/0 = 0. So ρ(0) never enters the series directly. Because every statement assumes N-periodicity, ρ(0) = ρ(N), so ρ(0) is still tied to a genuine term.
- The weight is 2^{−⌊k/2⌋}, not (√2)^{−k}: k = 2m and k = 2m+1 both get 2^{−m}.
- `HasSum f a` is Mathlib's unconditional sum (limit over finite subsets of ℕ, default summation filter `unconditional`). For periodic bounded ρ the terms are O(2^{−k/2}), so the series converges absolutely and HasSum agrees with the ordinary sum.

**Periodicity hypothesis.** "∀ k, ρ(k+N) = ρ(k)" with 0 < N. The hypotheses `120 ∣ N` (or `8 ∣ N`) **are not real restrictions**. An N-periodic ρ is also 120N-periodic, and none of the conclusions mention N. So every statement below applies to every periodic ρ, whatever its period.

**Block form (`patF2`, `bIdx`).** For n > 0 and a : Fin n → ℚ, `patF2 a k = a_{(k+n−1) mod n} · 2^{⌊(i+1)/2⌋}` with i = (k+n−1) mod n (natural subtraction n−1 is fine since n > 0). Write k = nj + i + 1 with 0 ≤ i < n. Then ρ(k) = a_i·2^{⌊(i+1)/2⌋}. When n is even, ⌊k/2⌋ = (n/2)j + ⌊(i+1)/2⌋, so

  S(patF2 a) = Σ_{j≥0} 2^{−(n/2)j} Σ_{i<n} a_i/(nj+i+1),

which is an ordinary BBP-type formula in base 2^{n/2} with n slots. (Only n = 24 and n = 120 are used.) patF2 a is n-periodic. At k = 0 it takes the value a_{n−1}·2^{n/2}.

**`termCount ρ`** is the number of k ∈ {0,1,…,119} with ρ(k) ≠ 0. It looks at a fixed window of 120 indices, not "per period":
- For a 120-periodic ρ it is the number of nonzero residues mod 120.
- For a 24-periodic ρ it is 5 × (nonzeros per period).
- For other periods it is just the count in that window. Index 0 counts if ρ(0) = ρ(N) ≠ 0.

So "40" means 40 nonzero coefficients per 120 consecutive indices, that is, per factor 2^60 of geometric decay. A base-4096 formula with 8 terms per period scores 40.

**`IsFValue x`** ("class F"): there exist N > 0 and a rational N-periodic ρ with S(ρ) = x. The class is closed under rational scaling (scale ρ), so ¬IsFValue(x) also rules out every nonzero rational multiple of x. It does not rule out algebraic multiples, or x plus other constants.

---

## 1. `PiFormula.theoremB`

**Plain statement.** There are three kinds of atom:
- P k, with base 1+i;
- Q k, with base −(1+i);
- R k e, with base i·2^{2^{e+1}} (that is, 4i, 16i, 256i, …).

For each atom a, let z_a = Φ_{2k+1}(base a) ∈ ℤ[i], where Φ_m is the m-th cyclotomic polynomial. Let c : Atom → ℚ be finitely supported, let q ∈ ℚ, and suppose

  Σ_{a ∈ supp c} c(a)·Arg(z_a) = qπ   (Arg is the principal argument, in (−π, π]).

Then:
- (i) c(a) = 0 for every a ∉ {P0, Q0, Q1, Q2};
- (ii) c(Q0) + c(Q2) = 0;
- (iii) q = (c(P0) + c(Q1))/2.

**Small cases (by hand).**
- z_{P0} = Φ₁(1+i) = i, so Arg = π/2.
- z_{Q1} = Φ₃(−1−i) = 2i − 1 − i + 1 = i, so Arg = π/2.
- z_{Q0} = Φ₁(−1−i) = −2−i.
- z_{Q2} = Φ₅(−1−i) = −4 + (2−2i) + 2i + (−1−i) + 1 = −2−i, the same Gaussian integer as Q0.

So (ii) and (iii) are exactly the obvious coincidences. The theorem says there are no others: π together with the arguments of all the non-exceptional z_a, and Arg(−2−i), are ℚ-linearly independent. In particular, no non-exceptional z_a is a positive real (Arg 0) or zero (Arg 0 = 0 in Mathlib). Either would make (i) false.

**Conventions.**
- `Finsupp.sum` is the sum over the (finite) support.
- Arg(0) = 0, and Arg of a negative real is +π. A non-exceptional atom of either kind would contradict (i) or need special handling. The claim implicitly says none exists.
- The relation is exact equality in ℝ, not modulo π.
- Only odd cyclotomic indices m = 2k+1 occur. k starts at 0.

**Edge cases.** c = 0 with q = 0 is trivially fine. Nothing is vacuous: there is a single universally quantified relation and three concrete conclusions.

**What it does not say.**
- Nothing about even-index cyclotomic values, about other bases (for example 2i or 8i), or about algebraic (rather than rational) coefficients.
- It is not stated in the `Unconditional` namespace, but the printed statement has no hypothesis.

**Doubts.** Which axioms the proof uses (a `#print axioms` check) cannot be seen from the statement. If a transcendence result is assumed as an axiom or hypothesis somewhere upstream, the print would not show it.

## 2. `Unconditional.value_formula`

**Plain statement.** Let ρ : ℕ → ℚ be periodic, and suppose S(ρ) = qπ for some q ∈ ℚ (this is what ρ ∈ `ratSpace N` means). Then

  S(ρ) = (7/12·ρ(1) + 1/8·ρ(2) + 1/6·ρ(3) − 7/12·ρ(7) + 1/6·ρ(9) − 1/8·ρ(14)) · π/4.

The coefficient expression is computed in ℚ and then cast to ℝ.

**Conventions.**
- `ratSpace N` includes q = 0, so zero relations are in it.
- Indices are literal positions k = 1, 2, 3, 7, 9, 14 of ρ (in block form, k = i+1).

**Checks (my computation).**
- rhoHuvent1 has ρ(3) = 1536 and ρ(14) = −2048, so the formula gives (256+256)π/4 = 128π. The series numerically sums to 128π.
- rhoHuvent2 has ρ(2) = 4096 and ρ(9) = 3072, giving 256π (numerically confirmed).
- rhoTak1 has ρ(2) = 16 and ρ(14) = −16, giving π. rhoTak2 has ρ(2) = 8, ρ(3) = 6, ρ(9) = 6 and ρ(14) = −8, giving π.

**Edge cases.** If those six coefficients vanish, the value is 0. The statement presupposes that the value is a rational multiple of π; it does not let one compute the value of a general periodic series.

**Does not say.** It does not say which ρ are in `ratSpace`, or that the six-term linear form is the only such form.

## 3. `Unconditional.theoremD_sharp`

**Plain statement.** Let ρ be periodic with S(ρ) ∈ ℚπ, and suppose ρ(k) = 0 for every k with gcd(k,120) ∈ {1,2,3}. Then ρ = c·zD for some c ∈ ℚ.

**What zD is (unfolded and computed).**
- zD = −2·L8 + 2·L10 + L24.
- Each L is built as rhoL(P)(k) = −Re(P(k)·U(k))/2, with U(k) = (−i)^{⌊k/2⌋}·(2 if k is even, else 1−i).
- I evaluated it on 0..239. zD is 120-periodic and has 43 nonzero values per period, all at k with gcd(k,120) ∈ {5,6,8,12,15,20,24,30,40,60}. It vanishes wherever gcd(k,120) < 4.
- Numerically S(zD) ≈ 0. L8, L10 and L24 each also sum to 0 numerically. So zD is a nonzero **zero relation**.

**Conventions.**
- `k.gcd 120 < 4` means gcd ∈ {1,2,3}. gcd(0,120) = 120, so k = 0 is never forced to vanish.
- c = 0 is allowed.

**Consequences and vacuity.** All six positions in `value_formula` (1, 2, 3, 7, 9, 14) have gcd with 120 in {1,2,3}. So any ρ satisfying the hypothesis has value 0 already by `value_formula`. The content of D is therefore that the space of such zero relations is at most one-dimensional, spanned by zD.

**Does not say.** The statement itself does not assert that zD satisfies the hypotheses, or that zD ≠ 0. So "sharp" (dimension exactly 1) is not part of this formal text. My numerical check suggests it is true, but it is not proved here.

## 4. `Unconditional.bailey_table`

**Plain statement.** For each listed triple (B, n, d), the ℚ-subspace

  Z(B,n) = { a ∈ ℚⁿ : Σ_{j≥0} 2^{−Bj} Σ_{i=0}^{n−1} a_i/(nj+i+1) = 0 }

has `finrank` d. There are 27 triples:
- n = B: (6,6,1), (12,12,1), (18,18,1), (24,24,1), (30,30,1), (36,36,1), (42,42,1), (48,48,1), (54,54,1), (60,60,1);
- n = 2B: (4,8,1), (8,16,1), (12,24,5), (16,32,1), (20,40,3), (24,48,5), (28,56,1), (30,60,1), (32,64,1), (36,72,5), (40,80,3), (42,84,1), (44,88,1), (48,96,5), (52,104,1), (56,112,1), (60,120,7).

**Conventions.**
- Denominators are nj+i+1, so they run over 1..n in the first block. There is no division by zero.
- This is the plain BBP form: no 2^{⌊(i+1)/2⌋} slot weights, unlike `seriesTerm`.
- HasSum is over the block index j, grouping n terms per block. The convergence is absolute, so the grouping is harmless.
- ℚⁿ is finite-dimensional, so `finrank` is the true dimension.

**Edge cases.** All listed B ≥ 4 and n ≥ 6, so nothing is degenerate.

**Does not say.** Nothing about pairs not in the list, or about relations with nonzero value.

## 5. `Unconditional.theoremE`

**Plain statement.** Let ρ be periodic and rational-valued, r ∈ ℚ with r ≠ 0, and S(ρ) = rπ. Then
- (a) #{k ∈ {0,…,119} : ρ(k) ≠ 0} ≥ 40, and
- (b) primeCost ρ ≥ 7/24.

**primeCost unfolded.**
- Let U be the set of c ∈ {0,…,119} with gcd(c,120) = 1. These are the 32 units mod 120; 0 is excluded since gcd(0,120) = 120.
- For c ∈ U, let x_c = the least x ∈ {1,…,120} with ρ(x·c) ≠ 0, or x_c = 0 if there is none (fuel 120, start x = 1).
- Then primeCost ρ = (1/32)·Σ_{c∈U} 1/x_c, with 1/0 = 0.

So primeCost is the average over the 32 unit residues c of the reciprocal of the first multiple index x at which ρ(xc) is nonzero. It lies in [0,1]. It equals 1 iff ρ(c) ≠ 0 for every unit c < 120. Note that ρ is evaluated at the integer x·c, not reduced mod 120, but periodicity makes this irrelevant when the period divides 120.

**Conventions that matter.**
- Window 0..119 for termCount (see the common section).
- The 1/0 = 0 default and the fuel cutoff can only lower primeCost, so they make the lower bound (b) stronger, not weaker. Similarly a sparse window only makes (a) stronger.

**Small cases (computed).** Huvent1 (support residues mod 24: {3,4,6,12,14,15,20,22}) and Huvent2 ({2,4,9,10,12,18,20,21}) both have termCount 40 and primeCost 5/12. rhoTak1 and rhoTak2 have termCount 42 and 50 and primeCost 1/2 each. None of these attains 7/24.

**Does not say.**
- It does not say that 7/24 is attained. Theorems (a) and (b) are separate bounds, not a joint optimum: a ρ with termCount 40 need not have primeCost 7/24.
- It says nothing for r = 0 (zero relations), or for formulas for algebraic multiples of π.

## 6. `Unconditional.termCount_eq_forty_iff`

**Plain statement.** Under the same hypotheses as E (ρ periodic, S(ρ) = rπ, r ∈ ℚ∖{0}):

  termCount ρ = 40 ⟺ ∃ a ∈ ℚ, a ≠ 0, and ρ = a·rhoHuvent1 or ρ = a·rhoHuvent2

(equality as functions on all of ℕ).

**The two sequences.**
- rhoHuvent1 = patF2 applied to the 24 coefficients huvent1, giving
  Σ_j 4096^{−j}(768/(24j+3) + 512/(24j+4) + 128/(24j+6) − 16/(24j+12) − 16/(24j+14) − 12/(24j+15) + 2/(24j+20) − 1/(24j+22)) = 128π.
- rhoHuvent2 gives
  Σ_j 4096^{−j}(2048/(24j+2) − 1024/(24j+4) + 192/(24j+9) + 128/(24j+10) + 32/(24j+12) − 4/(24j+18) − 4/(24j+20) − 3/(24j+21)) = 256π.
- Both are 24-periodic with 8 nonzeros per period, hence termCount = 5·8 = 40.

**Conventions.**
- "40" is per 120-index window. In base-4096 terms it is 8 terms per period.
- The ρ in the statement may have any period (for example 240). The theorem then claims ρ equals the Huvent multiple everywhere, which is a strong claim.

**Edge cases.** "a ≠ 0" is automatic from r ≠ 0. The (⇐) direction is easy given the computed counts.

**Does not say.** The two sequences are not identified as "Huvent's" by anything formal; that is only the name. It does not state the values 128π and 256π (I computed them).

## 7. `Unconditional.no_log23`

**Plain statement.** If ρ is rational and periodic (`8 ∣ N` is no restriction), q ∈ ℝ is algebraic over ℚ, and S(ρ) = q·log 23, then q = 0.

**Conventions.** `Real.log 23` is the usual natural logarithm (23 > 0). Note that `IsAlgebraic ℚ q` is for real q.

**Edge cases.** q = 0 is trivially consistent. The statement is not vacuous.

**Does not say.** Nothing about combinations such as q·log 23 + (other constants), or about non-periodic ρ.

## 8. `Unconditional.log_primes_below_100`

**Plain statement.** For a prime p < 100, IsFValue(log p) holds iff p ∈ {2,3,5,7,11,13,17,19,29,31,37,41,43,61,73}. So log p is **not** a class-F value for p ∈ {23,47,53,59,67,71,79,83,89,97}.

**Conventions.** It is about log p itself. By rational scaling it also covers nonzero rational multiples, but not algebraic multiples (except 23, by item 7).

**Does not say.** Nothing about primes ≥ 100.

## 9. `Unconditional.isFValue_log_rat_iff_pow`

**Plain statement.** For y ∈ ℚ with y > 0: IsFValue(log y) holds iff there exist k ≥ 1, n ∈ ℕ, g ∈ ℤⁿ and e ∈ ℤⁿ with every g_i ∈ B and y^k = Π_i g_i^{e_i} in ℚ (integer exponents). The set of base numbers is

  B = {2} ∪ {2^m − 1 : m ≥ 1} ∪ {2^{2k+1} − 2^{k+1} + 1 : k ≥ 0} ∪ {2^{2k+1} + 2^{k+1} + 1 : k ≥ 0}.

Equivalently, y lies in the saturation (in ℚ_{>0}^×) of the subgroup generated by B.

**Small cases.**
- m = 1 gives 1 ∈ B, which is harmless.
- k = 0 gives 1 and 5. k = 1 gives 5 and 13. k = 2 gives 25 and 41.
- These are the Aurifeuillean factors of 2^{4k+2}+1.
- All elements of B are ≥ 1, so negative exponents never meet 0.

**Edge cases.** y = 1: log 1 = 0 is an F-value (ρ = 0), and the right side holds with n = 0 (empty product 1). Both sides are true, consistently.

**Does not say.** It gives no effective test by itself; the right side is an infinite search.

## 10. `Unconditional.isFValue_log_prime_classification`

**Plain statement (assuming `orderOf 2` means the order of 2 in (ℤ/ℓℤ)^×; see Doubts).** Let ℓ be prime and d = ord_ℓ(2). Define the primitive part:
- If d ≡ 4 (mod 8), then with n = d/4 (odd), primPart ℓ = A⁺(n) if ℓ | A⁺(n), else A⁻(n). Here A^±(n) = N_{ℤ[i]/ℤ}(Φ_n(±(1+i))), the two Aurifeuillean halves of Φ_d(2).
- Otherwise primPart ℓ = Φ_d(2).

Then IsFValue(log ℓ) holds iff either
- ℓ | 2(2^60 − 1), or
- for every prime q ≠ ℓ with q | primPart ℓ: q | d and IsFValue(log q).

**Checks.**
- ℓ = 23: d = 11, Φ₁₁(2) = 2047 = 23·89, and 89 ∤ 11. So log 23 is not in F, consistent with item 8.
- ℓ = 19: d = 18, Φ₁₈(2) = 57 = 3·19, with 3 | 18 and log 3 ∈ F. So log 19 is in F, consistent.
- ℓ = 37: d = 36 ≡ 4 (mod 8), and 4033 = 37·109 splits into Aurifeuillean halves 37 and 109. So primPart = 37, the ∀ clause is vacuously true, and log 37 is in F, consistent.

**Conventions.**
- The ∀-clause is vacuously true when primPart has no prime factor besides ℓ. This is intended, not a bug.
- The criterion is recursive in IsFValue. It is an iff, not an algorithm, though the recursion goes to primes q | d < ℓ.
- ℓ = 2 is covered by the first disjunct.

**Doubts.**
- The printed `orderOf 2` (both in the statement and in `primPart`) shows no type. If it were orderOf (2 : ℕ) or (2 : ℤ), then 2 has infinite order, so orderOf = 0. Then Φ₀ = 1 (Mathlib `cyclotomic_zero`), so primPart = 1, the second disjunct is vacuously true, and the statement would claim log ℓ ∈ F for every prime ℓ. That contradicts item 8 (23).
- So the only coherent reading is (2 : ZMod ℓ), but this must be confirmed from source or with `pp.numericTypes`. Please check.

## 11. `Unconditional.not_isFValue_arctan_two_sevenths`

**Plain statement.** There is no N > 0 and N-periodic rational ρ with Σ_{k≥1} ρ(k)/(2^{⌊k/2⌋}k) = arctan(2/7). Here 2/7 is real division, ≈ 0.2857.

By scaling, the same holds for every nonzero rational multiple. It is not shown for algebraic multiples or for arctan(2/7) + rπ.

## 12. `Unconditional.pairCost_ge`

**Plain statement.** Let ρ₁ and ρ₂ be periodic and rational, r ∈ ℚ with r ≠ 0, S(ρ₁) = S(ρ₂) = rπ (the **same** r), and ρ₁ ≠ ρ₂ as functions. Then pairCost(ρ₁,ρ₂) ≥ 60, where

  pairCost = #{k < 120 : ρ₁(k) ≠ 0 or ρ₂(k) ≠ 0} + #{k < 120 : ρ₁(k) ≠ 0 and ρ₁(k) = ρ₂(k)}
       = |supp₁ ∪ supp₂| + |{k : ρ₁(k) = ρ₂(k) ≠ 0}|
       = |supp₁| + |supp₂| − |{k : both nonzero, ρ₁(k) ≠ ρ₂(k)}|.

**What a "pair" and its cost are.**
- A pair is any two distinct periodic formulas for the same rational multiple of π.
- The cost counts each slot used by either formula once, and counts a second time each slot where both formulas use the same nonzero coefficient. Slots shared with different coefficients count once.
- Everything is restricted to the window k = 0..119.
- The cost is not normalised by period. For 120-periodic sequences it is per period (base 2^60).

**Conventions and edge cases.**
- "Same r" is a normalisation. A pair for r₁π and r₂π can be rescaled to the same r, but rescaling changes which coefficients coincide, so the cost of an unnormalised pair is not covered.
- ρ₁ ≠ ρ₂ could hold only outside the window (period > 120). The bound is still claimed.
- r = 0 pairs are not covered.

**Does not say.** It does not say the bound is attained; that is the next item.

## 13. `Unconditional.checkedPair`

**Plain statement.** It is the conjunction of:
- (1) exactly the statement of `pairCost_ge`;
- (2) S(rhoTak1) = π;
- (3) S(rhoTak2) = π;
- (4) pairCost(rhoTak1, rhoTak2) = 60.

**The sequences.**
- rhoTak_j = patF2 (n = 120) of coefficients a_i = tak_jNum[i]/2^57. `List.getD` defaults to 0 beyond the list, but both lists have exactly 120 entries (checked).
- So each is a base-2^60, 120-slot BBP-type formula.

**My computation.**
- Both sums are numerically π. This matches `value_formula`: Tak1 gives (2+2)π/4, and Tak2 gives (1+1+1+1)π/4.
- Supports: |supp₁| = 42, |supp₂| = 50, union 58, intersection 34.
- Equal nonzero coefficients occur at exactly k = 30 (value 4) and k = 90 (value −4).
- Cost = 58 + 2 = 60, as claimed.

**Conventions.**
- The statement does not itself assert rhoTak1 ≠ rhoTak2 or periodicity. Both are evident: patF2 output is 120-periodic, and ρ₁(3) = 0 ≠ 6 = ρ₂(3). So the pair is admissible in (1) with N = 120 and r = 1, and (1)+(4) say the minimum 60 is attained.
- The name "Takahashi" is only a name. Nothing formal ties the lists to a published formula.

## 14. `Unconditional.not_isFValue_log_38737`

**Plain statement.** log 38737 is not a class-F value. By my trial division, 38737 has no prime factor below 197 and 197² > 38737, so 38737 is prime.

The statement is just non-membership. It does not say whether 38737 appears in any external list; that would be a claim outside the formal text.

---

## Definitions cut for length

None of the definitions is marked as cut. `tak1Num` and `tak2Num` are printed as nested `have y := …` chains. They are complete, and I reconstructed both lists in full, each of length 120.

The only gap in the printed text is the missing type ascription on `orderOf 2` (item 10). Proof terms `⋯` (for example `rhoHuvent1._proof_2 : 0 < 24`) are irrelevant to meaning.

## General doubts

1. Which axioms each theorem depends on is not visible in the statements.
2. In item 10: confirm `orderOf (2 : ZMod ℓ)`.
3. In D: the statement does not include zD ∈ ratSpace or zD ≠ 0. If "sharp" (dimension exactly 1) is claimed, it is not in this formal text.
