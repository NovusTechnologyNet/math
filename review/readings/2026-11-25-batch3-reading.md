# Independent reading of batch 3 (16 statements)

I read only `view_batch3.txt`. I relied on standard Mathlib meanings: `HasSum f x` in ℝ is unconditional convergence of `∑ f` to `x`. For every series here the terms decay geometrically, so this is the same as absolute convergence of the ordinary sum. `x / 0 = 0`. `k / 2` on ℕ is the floor. `Transcendental ℚ x` means `¬ IsAlgebraic ℚ x`. A `Finset.filter` card counts the indices that satisfy the predicate.

I ran two numerical checks in plain Python, to about 16 digits. They are sanity checks, not part of any statement:
- `rhoGregory` gives a base-3 series value of √3·π.
- `rhoSecond` gives a base-3 series value of √3·π.

## Summary table

| Theorem | Plain statement | Confidence |
|---|---|---|
| `Base3.isF3Value_log_rat_iff_pow` | For rational y > 0: log y is the sum of some periodic-rational base-3 series ⇔ some positive power y^k is a finite product of integer powers of numbers in the set G₃ = {3} ∪ {3^m−1 : m≥1} ∪ {3^(2k+1) ∓ 3^(k+1) + 1 : k≥0}. | high |
| `Base3.not_isF3Value_pi` | π is not the sum of any series ∑_{k≥1} ρ(k)/(3^⌊k/2⌋·k) with ρ rational and periodic. | high |
| `Base3.isF3Value_mul_pi_iff` | For real algebraic γ: γπ is such a base-3 value ⇔ γ ∈ ℚ·√3. | high |
| `Base3.theoremC3` | For N > 0 with 12 ∣ N: every N-periodic rational ρ whose base-3 series sums to (algebraic)·π is in fact 12-periodic. These ρ form a ℚ-space of dimension 3. Those whose series sums to 0 form a space of dimension 2. | high |
| `Base3.theoremE3` | If a periodic rational ρ has base-3 sum γπ with γ algebraic and γ ≠ 0, then at least 6 of ρ(0),…,ρ(11) are non-zero. Exactly 6 happens iff ρ is a rational multiple of `rhoGregory` or of `rhoSecond`. | high |
| `Base5.eq_zero_of_hasSum_mul_pi` | In base 5, if a periodic rational ρ has series sum γπ with γ algebraic (γ = 0 allowed), then ρ is identically 0. | high |
| `Base5.isF5Value_log_rat_iff_pow` | For rational y > 0: log y is a base-5 value ⇔ some y^k (k ≥ 1) is a finite product of integer powers of elements of an explicit set G₅ ⊂ ℚ. | high |
| `BaseB.eq_zero_of_hasSum_mul_pi` | The same as the base-5 statement, for every natural base b ≥ 5. | high |
| `BaseB.transcendental_of_isFBValue` | For b ≥ 2, every non-zero value of a periodic-rational series ∑ ρ(k)/(b^⌊k/2⌋·k) is transcendental. | high |
| `BaseB.bailey_pi_iff` | For a fixed natural b ≥ 2: some Bailey-form series ∑_j b^(−Bj) ∑_{i<N} c_i/(Nj+i+1) (with B, N, c and q ≠ 0 all chosen freely) sums to qπ ⇔ b is a power of 2. | high |
| `BaseB.bailey_int_pi_iff` | The same for an integer base β with \|β\| ≥ 2: ⇔ \|β\| is a power of 2. | high |
| `BaseB.no_pi_bailey_ten` | In base 10, every Bailey-form series that sums to qπ with q rational has q = 0. | high |
| `BaseB.bailey_log_self_iff` | For b ≥ 2: some Bailey-form series in base b sums to log b ⇔ b is a power of 2 or a power of 3. | high |
| `BaseB.no_log_nat_bailey` | If b ≥ 2 is neither a power of 2 nor of 3, then no Bailey-form series in base b sums to qπ + q′·log n, for q, q′ rational with q′ ≠ 0 and n ≥ 2 natural. | high |
| `BaseB.terms_per_bit` | If a Bailey-form series in base b sums to qπ with q ≠ 0, then b = 2^e and 2·e·B ≤ 3·#{i : c_i ≠ 0}. In words: at least 2/3 of a non-zero coefficient per bit of b^B. | high |
| `BaseB.terms_per_bit_attained` | There are c ∈ ℚ^24 and q ≠ 0 with ∑_j 2^(−12j) ∑_{i<24} c_i/(24j+i+1) = qπ and exactly 8 of the c_i non-zero. | high |

## Shared definitions, unfolded

- **seriesTerm3 ρ k** = ρ(k) / 3^⌊k/2⌋ / k, as a real number.
  - At k = 0 the division by (0 : ℝ) makes the term 0, whatever ρ(0) is.
  - So the series is ∑_{k≥1} ρ(k)/(3^⌊k/2⌋·k): base 3 per two indices, that is base √3 per index, with denominator exactly k.
  - **seriesTerm5** is the same with 5. **seriesTermB b** is the same with b, cast to ℝ.
- **IsF3Value x** ⇔ ∃ N ≥ 1 and ρ : ℕ → ℚ with ρ(k+N) = ρ(k) for all k, and ∑_{k≥1} ρ(k)/(3^⌊k/2⌋ k) = x. **IsF5Value** and **IsFBValue b** are the same.
  - The period N is existential.
  - ρ(0) never enters the sum directly. It equals ρ(N), which does enter.
- **baileyBlock b B N a j** = ∑_{i=0}^{N−1} a_i / (b^(B·j) · (N·j + i + 1)). `HasSum` is taken over j ∈ ℕ, j starting at 0.
  - The denominators N·j+i+1 run over every positive integer exactly once. So the series is ∑_{n≥1} a_{(n−1) mod N} · b^(−B⌊(n−1)/N⌋) / n.
  - No denominator is 0.
  - The power b^(B·j) is a real power with natural exponent, and b ≥ 2 throughout, so nothing divides by zero.
- **baileyBlockInt β B N a j** is the same with a real β cast from ℤ. For β < 0, β^(B·j) = (−1)^(Bj)·|β|^(Bj): the terms alternate in sign when B is odd and do not when B is even.

---

## 1. `PiFormula.Base3.Unconditional.isF3Value_log_rat_iff_pow`

**Plain statement.** Let y ∈ ℚ with y > 0. Then log y is an F3-value (some N ≥ 1 and N-periodic ρ : ℕ → ℚ with ∑_{k≥1} ρ(k)/(3^⌊k/2⌋ k) = log y) if and only if both of these hold:
- there is a natural k ≥ 1, and
- there are finitely many integers g_1,…,g_n ∈ G₃ (repetition allowed, n = 0 allowed) and integer exponents e_1,…,e_n ∈ ℤ with y^k = ∏ g_i^(e_i) in ℚ.

The set G₃ is the union of:
- {3},
- {3^m − 1 : m ≥ 1} = {2, 8, 26, 80, 242, …},
- {3^(2k+1) − 3^(k+1) + 1 : k ≥ 0} = {1, 19, 217, …},
- {3^(2k+1) + 3^(k+1) + 1 : k ≥ 0} = {7, 37, 271, …}.

Equivalently, y lies in the saturation (the isolator) of the subgroup of ℚ_{>0}^× generated by G₃.

**Conventions.**
- The g_i are integers cast into ℚ, and `^ e i` is `zpow`, so negative exponents give reciprocals.
- No element of G₃ is 0 (the smallest are 1 and 2), so `0^(negative)` never occurs.
- All arithmetic in G₃ is in ℤ, so there is no truncated subtraction.
- k = 0 of the "minus" family gives 1 ∈ G₃. This is harmless.
- y^k uses a natural exponent.

**Edge cases.**
- y = 1: both sides hold trivially (n = 0, or ρ = 0).
- The k ≥ 1 requirement is essential: k = 0 would make the right side always true.
- k really matters. For example 3^5 − 1 = 242 = 2·11², so 11² = 242/2 is in the group. That puts y = 11 in via k = 2 (I did not check whether 11 itself is in the group).
- Neither direction is trivial.
  - "⇐" says each generator's logarithm is a value, which needs explicit series.
  - "⇒" says nothing else is a value. This is the deep, Baker-type direction.

**What it does not say.**
- Only logarithms of rationals are covered. It says nothing about ℚ-combinations of log y with π.
- It says nothing about other series shapes, such as other exponents or denominators other than k.

**Doubts.** None about the reading.

## 2. `PiFormula.Base3.Unconditional.not_isF3Value_pi`

**Plain statement.** There is no N ≥ 1 and N-periodic rational ρ with ∑_{k≥1} ρ(k)/(3^⌊k/2⌋ k) = π.

**Conventions.** These are as above. Only π itself is excluded here. Rational multiples of π are excluded by the next theorem (γ = q with q ≠ 0 is not in ℚ√3).

**Edge cases.** The statement is a plain non-existence statement, so it is not vacuous.

**What it does not say.** It does not exclude √3·π, which is in fact a value. It does not exclude other shapes of base-3 series.

## 3. `PiFormula.Base3.Unconditional.isF3Value_mul_pi_iff`

**Plain statement.** For every real γ algebraic over ℚ: γπ is an F3-value ⇔ ∃ q ∈ ℚ with γ = q·√3 (`√3` is `Real.sqrt 3`).

**Edge cases.**
- γ = 0 gives q = 0 on the right and ρ = 0 on the left, so this case is trivial.
- "⇐" amounts to exhibiting one series for √3π and scaling it. My numerical check shows that `rhoGregory` gives √3π.
- "⇒" is the substantive direction.

**What it does not say.** The γ is restricted to algebraic numbers. It says nothing about which transcendental multiples of π are values, for example (log 2/π)·π.

## 4. `PiFormula.Base3.Unconditional.theoremC3`

**Plain statement.** Let N ∈ ℕ with N > 0 and 12 ∣ N. Define two sets of N-periodic rational sequences ρ : ℕ → ℚ (full sequences, ρ(0) included):
- A_N = {ρ : ρ is N-periodic and ∃ real algebraic γ with ∑_{k≥1} ρ(k)/(3^⌊k/2⌋ k) = γπ},
- Z_N = {ρ : ρ is N-periodic and ∑_{k≥1} ρ(k)/(3^⌊k/2⌋ k) = 0}.

Both are ℚ-subspaces of ℚ^ℕ, and Z_N ⊆ A_N (take γ = 0). Then:
- (i) every ρ ∈ A_N satisfies ρ(k+12) = ρ(k) for all k;
- (ii) dim_ℚ A_N = 3;
- (iii) dim_ℚ Z_N = 2.

**Conventions.**
- The space is a subspace of the N-dimensional space of N-periodic sequences, viewed inside ℕ → ℚ.
- ρ(0) is a coordinate of the vector, but it is determined by periodicity (ρ(0) = ρ(N)), so no spurious free coordinate arises from the term at k = 0 being 0.
- `Module.finrank` is the true dimension, since A_N is finite-dimensional, being inside the N-periodic sequences. (finrank would be 0 for an infinite-dimensional space, but that does not apply here.)
- γ ranges over the real algebraic numbers, including irrational ones.

**Edge cases.**
- The smallest case is N = 12, where (i) is trivial.
- For a general multiple of 12, (i) says that larger periods give nothing new.
- (ii) and (iii) together say that A_N/Z_N is one-dimensional: all values are rational multiples of one number (√3π, by statement 3).
- The hypotheses are satisfiable.

**What it does not say.**
- It says nothing directly for N not divisible by 12. One can reduce to 12N, but the statement does not do so.
- It does not name bases of the spaces.
- It is only about values that are algebraic multiples of π. For example, it says nothing about the space of ρ giving logarithms.

## 5. `PiFormula.Base3.Unconditional.theoremE3`

**Plain statement.** Let N ≥ 1 and let ρ : ℕ → ℚ be N-periodic. Let γ be real, algebraic and non-zero, with ∑_{k≥1} ρ(k)/(3^⌊k/2⌋ k) = γπ. Let T(ρ) = #{k ∈ {0,1,…,11} : ρ(k) ≠ 0}. Then:
- (a) T(ρ) ≥ 6;
- (b) T(ρ) = 6 ⇔ ∃ a ∈ ℚ with ρ = a·ρ_G or ρ = a·ρ_S, as functions on all of ℕ.

The two sequences are:
- ρ_G(k) = 6·(−1)^⌊k/2⌋ for k odd and 0 for k even. This is period 4: the values at k = 1, 3, 5, 7, 9, 11 are +6, −6, +6, −6, +6, −6.
- ρ_S(k) depends on k mod 12: it is 18 for residues 2, 3, 4, it is −18 for residues 8, 9, 10, and it is 0 otherwise. This is period 12.

Both have exactly 6 non-zero values in {0,…,11}. Both give the value √3π (my numerical check, to machine precision). ρ_G is the Gregory series for 6√3·arctan(1/√3).

**Conventions (important).**
- **What is counted:** non-zero entries among ρ(0),…,ρ(11), a fixed window of 12 indices.
  - This includes ρ(0), which is not a term of the series (the k = 0 term is forced to 0 by /0).
  - For a 12-periodic ρ, ρ(0) = ρ(12), so the window is equivalent to counting k = 1…12, a full period. The count is then "non-zero terms per 12 indices", i.e. per decay factor 3^6.
  - The count is **not** normalised by the given period N, nor by the minimal period. ρ_G has minimal period 4 with 2 non-zeros per period, and it is counted as 6.
- **Arbitrary period.** The theorem allows any period N, not only multiples of 12. The window of 12 is the right normalisation only because such ρ are automatically 12-periodic. (N-periodic implies 12N-periodic, which by C3(i) implies 12-periodic.) That fact is not part of this statement, but it holds by C3, so I see no loophole.
- The count is a ℕ-valued `Finset.card`, compared with the natural number 6.

**Edge cases and the uniqueness clause.**
- γ ≠ 0 excludes ρ = 0.
- In (b), "⇐" with a = 0 would give ρ = 0, but that contradicts γ ≠ 0. So under the hypotheses a ≠ 0 automatically, and then T(a·ρ_G) = T(a·ρ_S) = 6.
- "⇐" is easy (counting).
- "⇒" is the real uniqueness claim: up to a rational scalar there are exactly two optimal sequences. Equality is as functions ℕ → ℚ, a fixed phase: no shifts or other representatives are allowed.
- The hypotheses are satisfiable (ρ_G, N = 4, γ = √3).

**What it does not say.**
- It is only for this series shape (denominator k, base 3 per two indices).
- It is only for values that are non-zero algebraic multiples of π.
- It does not bound terms per bit or per base-3 digit in any other normalisation.

**Doubts.** None about the reading.

## 6. `PiFormula.Base5.Unconditional.eq_zero_of_hasSum_mul_pi`

**Plain statement.** For N ≥ 1, an N-periodic ρ : ℕ → ℚ and a real algebraic γ: if ∑_{k≥1} ρ(k)/(5^⌊k/2⌋ k) = γπ, then ρ(k) = 0 for every k ∈ ℕ.

**Edge cases.** γ = 0 is allowed. So the statement also says **there is no non-zero periodic ρ whose base-5 series sums to 0** (no "zero relations"), in addition to saying that no non-zero algebraic multiple of π is a value. ρ = 0 is meant everywhere, including ρ(0), which is fine because ρ(0) = ρ(N).

**What it does not say.** It says nothing about values such as logarithms, or about other shapes in base 5.

## 7. `PiFormula.Base5.Unconditional.isF5Value_log_rat_iff_pow`

**Plain statement.** For y ∈ ℚ with y > 0: log y is an F5-value (∑_{k≥1} ρ(k)/(5^⌊k/2⌋ k), with ρ rational and periodic) ⇔ ∃ k ≥ 1, finitely many g_1,…,g_n ∈ G₅ ⊂ ℚ and e_i ∈ ℤ with y^k = ∏ g_i^(e_i).

The set G₅ is the union of:
- (5^m − 1)/5^m for m ≥ 1: 4/5, 24/25, 124/125, …;
- L(h)/5^(2h) and M(h)/5^(2h) for **odd** h, where
  - L(h) = 5^(2h) + 3·5^h + 1 − 5^((h+1)/2)·(5^h+1),
  - M(h) = 5^(2h) + 3·5^h + 1 + 5^((h+1)/2)·(5^h+1),
  - with integer arithmetic, and (h+1)/2 exact because h is odd.
  - h = 1 gives 11/25 and 71/25; h = 3 gives 12851/5^6 = 71·181/5^6 and 19151/5^6 = 11·1741/5^6.

**Conventions.**
- The g_i are rationals with integer exponents (`zpow`).
- All g_i > 0 (L(1) = 11, and L(h) > 0 for larger odd h), so no zero or sign issue arises.
- Unlike the base-3 set, **5 itself is not listed** as a generator, and neither are the plain integers 5^m − 1. Only the quotients (5^m − 1)/5^m are listed.

**Edge cases.** y = 1 is trivial. The k ≥ 1 requirement is essential.

**What it does not say.** It is only for rational y. It says nothing about π-combinations.

**Doubts.** Is log 5 a base-5 value, i.e. is 5 in the saturated group generated by G₅? I did not settle this. Every generator has negative 5-adic valuation together with other primes, and I found no obvious combination that isolates 5. The statement is fine either way, but anyone quoting "log 5" should check.

## 8. `PiFormula.BaseB.Unconditional.eq_zero_of_hasSum_mul_pi`

**Plain statement.** For every natural b ≥ 5, N ≥ 1, N-periodic ρ : ℕ → ℚ and real algebraic γ: if ∑_{k≥1} ρ(k)/(b^⌊k/2⌋ k) = γπ, then ρ ≡ 0.

**Edge cases.**
- γ = 0 is allowed, so the statement also says there are no zero relations, for every b ≥ 5.
- The range includes b = 8, 16 (powers of 2) and b = 9, 25 (perfect squares).
  - For b = 9 the shape is equivalent to ∑ σ(k)/(3^k k) with σ periodic rational. The statement then says: no non-zero rational periodic σ makes ∑ σ(k) 3^(−k)/k equal to an algebraic multiple of π, including 0.
  - For b = 16 it says the same of ∑ σ(k) 4^(−k)/k.
- b = 2, 3, 4 are excluded.

**What it does not say.** It is only for denominator k and exponent ⌊k/2⌋. It is not the Bailey block form with a free B and N, which is a different family (see 10 to 15).

## 9. `PiFormula.BaseB.Unconditional.transcendental_of_isFBValue`

**Plain statement.** For every natural b ≥ 2 and real x: if x = ∑_{k≥1} ρ(k)/(b^⌊k/2⌋ k) for some N ≥ 1 and N-periodic ρ : ℕ → ℚ, and x ≠ 0, then x is not algebraic over ℚ.

**Edge cases.** b = 2 is the smallest base. The x ≠ 0 hypothesis is necessary (x = 0 from ρ = 0). The statement is not vacuous.

**What it does not say.** It says nothing about whether two such values are algebraically independent, or about other series shapes.

## 10. `PiFormula.BaseB.bailey_pi_iff`

**Plain statement.** Fix a natural b ≥ 2. Then the following two conditions are equivalent:
- **[∃ B ≥ 1, ∃ N ≥ 1, ∃ c ∈ ℚ^N, ∃ q ∈ ℚ with q ≠ 0, such that ∑_{j≥0} b^(−Bj) ∑_{i=0}^{N−1} c_i/(Nj+i+1) = qπ]**,
- **[∃ e ∈ ℕ with b = 2^e]**.

Since b ≥ 2, e ≥ 1 automatically.

**Quantifiers.**
- The base b is fixed, outside the iff.
- The exponent step B, the block length N, the coefficients c and the multiplier q are all existential on the left.
- The right side is existential in e.

**Directions.**
- "⇐": for b = 2^e, some Bailey-form formula for a non-zero rational multiple of π exists. Example: take B = 4, so b^B = 16^e, and spread the BBP digits.
- "⇒": for b not a power of 2 (b = 3, 5, 6, 10, …), no choice of B, N, c gives a non-zero **rational** multiple of π.
- Neither direction is trivial. "⇐" needs a construction for each e.

**Conventions.**
- The index i starts at 0, so the denominators are Nj+1, …, Nj+N. There is no zero denominator.
- `HasSum` is over j, with the block sums formed first. The series is absolutely convergent, so this makes no difference.

**What it does not say.**
- It covers only rational multiples q·π, not algebraic multiples. For b = 3, √3·π is not excluded.
- It covers only degree 1: one linear denominator Nj+i+1, no powers (Nj+i+1)^s, and no several interleaved shapes.
- It covers only a natural base. The integer base is the next statement.

## 11. `PiFormula.BaseB.bailey_int_pi_iff`

**Plain statement.** Fix β ∈ ℤ with |β| ≥ 2. Then [∃ B ≥ 1, N ≥ 1, c ∈ ℚ^N, q ∈ ℚ∖{0} with ∑_{j≥0} β^(−Bj) ∑_{i<N} c_i/(Nj+i+1) = qπ] ⇔ [∃ e, |β| = 2^e]. The quantifiers are as in 10.

**Conventions.** For β < 0, β^(Bj) = (−1)^(Bj)|β|^(Bj). The left side lets B be chosen:
- an even B removes the sign;
- an odd B can be absorbed by doubling N and B (alternating signs become a block of length 2N with coefficients c, −c).

So this is essentially equivalent to statement 10 applied to |β|, a mild extension. Positive β is included and is just statement 10 again.

**What it does not say.** As in 10. It is not a statement about bases such as −3 having some other kind of formula.

## 12. `PiFormula.BaseB.no_pi_bailey_ten`

**Plain statement.** For all B ≥ 1, N ≥ 1, c ∈ ℚ^N and q ∈ ℚ: if ∑_{j≥0} 10^(−Bj) ∑_{i<N} c_i/(Nj+i+1) = qπ, then q = 0.

**Edge cases.**
- The conclusion is q = 0, **not** c = 0. The statement allows (and does not decide) zero relations, i.e. non-zero c with sum 0.
- It follows from the "⇒" direction of 10 with b = 10.

**What it does not say.** It does not exclude algebraic irrational multiples of π, such as √2·π. It is only for this degree-1 block shape.

## 13. `PiFormula.BaseB.bailey_log_self_iff`

**Plain statement.** Fix a natural b ≥ 2. Then [∃ B ≥ 1, N ≥ 1, c ∈ ℚ^N with ∑_{j≥0} b^(−Bj) ∑_{i<N} c_i/(Nj+i+1) = log b] ⇔ [b = 2^e for some e, or b = 3^e for some e].

**Conventions and quantifiers.**
- b is fixed; B, N and c are existential.
- The target is exactly log b, with coefficient 1. Since c can be scaled by any rational, this is the same as "some non-zero rational multiple of log b is a value".
- e = 0 is excluded by b ≥ 2.

**Directions.**
- "⇐": every power of 2 or of 3 has a formula. Example for b = 3: log(3/2) = ∑ 1/(n 3^n) and log(9/8) = ∑ 1/(n 9^n), so log 3 = 3·log(3/2) − log(9/8). Both pieces are Bailey-form in base 3, with B = 1 and B = 2.
- "⇒": no other base has one. So b = 5, 6, 7, 10, 12, … have none.

**What it does not say.** It concerns log b of the base itself only, not log n for other n. That is partly covered by 14.

## 14. `PiFormula.BaseB.no_log_nat_bailey`

**Plain statement.** Let b ≥ 2 be a natural number such that b ≠ 2^k and b ≠ 3^k for every k ∈ ℕ. Let B ≥ 1, N ≥ 1 and c ∈ ℚ^N, and let q, q′ ∈ ℚ with **q′ ≠ 0** (q may be 0). Let n ≥ 2 be a natural number. Then ∑_{j≥0} b^(−Bj) ∑_{i<N} c_i/(Nj+i+1) ≠ qπ + q′·log n.

**Conventions.**
- k = 0 in the hypotheses only excludes b = 1, which is already excluded.
- n is a natural number ≥ 2, so log n > 0.
- Only one logarithm, of a natural number, appears.

**Edge cases.**
- n = b is included, which strengthens "⇒" of 13 by allowing an extra rational π term.
- The hypotheses are satisfiable (b = 5).
- Values that are logarithms of non-integer rationals are not excluded and do exist. For example, log(5/4) = ∑ 1/(m 5^m) in base 5.

**What it does not say.**
- It does not exclude q′·log(r) for rational non-integer r, nor combinations of two or more logarithms.
- It does not exclude algebraic, non-rational coefficients.
- It says nothing for bases that are powers of 2 or 3.

## 15. `PiFormula.BaseB.terms_per_bit`

**Plain statement.** Let b ≥ 2, B ≥ 1, N ≥ 1, c ∈ ℚ^N and q ∈ ℚ with q ≠ 0, such that ∑_{j≥0} b^(−Bj) ∑_{i<N} c_i/(Nj+i+1) = qπ. Then ∃ e ∈ ℕ with b = 2^e and 2·(e·B) ≤ 3·#{i < N : c_i ≠ 0}.

**Conventions (normalisation).**
- The inequality is between natural numbers, with no division, so there is no floor issue.
- e·B = log₂(b^B) is the number of bits gained per block (one block = one j).
- #{i : c_i ≠ 0} is the number of non-zero terms per block.
- So the content is: (non-zero terms per block)/(bits per block) ≥ 2/3.
- The ratio is invariant under re-blocking (B, N, c) → (2B, 2N, …), since both counts double.

**Small cases.**
- BBP: b = 16, B = 1, N = 8, c = (4, 0, 0, −2, −1, −1, 0, 0), q = 1. Here e = 4, and 2·4 = 8 ≤ 3·4 = 12. That is 1 term per bit.
- Statement 16 gives 2·12 = 24 = 3·8, equality.

**Edge cases.** The theorem also contains the "⇒" direction of 10 (b must be a power of 2). The hypotheses are satisfiable.

**What it does not say.**
- It covers only rational multiples of π.
- It covers only this degree-1 block shape. In particular it does not count terms for formulas with several denominators per index, or with powers like (8k+1)^2, or with exponent steps that are not uniform in j.
- It does not bound the total number of non-zero coefficients in any other normalisation, such as per decimal digit or counting only the coefficients that are not ±1.

## 16. `PiFormula.BaseB.terms_per_bit_attained`

**Plain statement.** There exist c : Fin 24 → ℚ and q ∈ ℚ with q ≠ 0 such that:
- ∑_{j≥0} 2^(−12j) ∑_{i=0}^{23} c_i/(24j+i+1) = qπ, and
- exactly 8 of c_0,…,c_23 are non-zero.

This is the equality case 2·(1·12) = 24 = 3·8 of statement 15, so the bound 2/3 is sharp.

**Edge cases.** This is an existence statement, so it is not vacuous. It needs one explicit c.

**What it does not say.** It does not say this c is unique, or that b = 2, B = 12 is the only way to attain the bound.

---

## Overall points for the authors

1. **theoremE3's count** is "non-zero entries among ρ(0..11)", a fixed window that includes ρ(0) (not itself a term) and is independent of the given period N.
   - It is the right normalisation only because algebraic-multiple-of-π sequences are automatically 12-periodic (C3(i)). That fact is not part of E3.
   - The uniqueness is equality of whole functions up to a rational scalar, with no shifts.
   - So "6 terms" means 6 per 12 indices, i.e. per factor 3^6, for a sequence like ρ_G of minimal period 4.
2. **Base-5 and base-b ≥ 5 eq_zero** allow γ = 0. So each also asserts that there are no zero relations at all. This is stronger than "no formula for π", and it also covers b = 8, 9, 16, 25.
3. **Every Bailey-form "iff"** (10, 11, 12, 15) is about non-zero rational multiples qπ only. Algebraic multiples such as √3π for b = 3 are not addressed.
   - no_pi_bailey_ten concludes q = 0, not c = 0.
   - no_log_nat_bailey excludes only qπ + q′·log n with a single natural n ≥ 2.
4. **Open question (7):** is 5 itself in the saturated group generated by the base-5 set, i.e. is log 5 a base-5 value? The generator list does not include 5, unlike the base-3 list, which includes 3. I could not settle this.
